extern crate log;
extern crate simple_logger;
use log::debug;
use crate::Terminate::{RanOffEnd, ProgramHalted, Unimplemented, StackEmpty, RegisterInvalid};
use std::fs;
use std::fmt::Debug;
use std::process::{Command, Output};

#[cfg(test)]
mod tests {
    use super::*;
    use super::instruction_set::*;

    #[test]
    fn test_interpreter_halt() {
        let program: &Vec<Box<dyn Instruction>> = &vec!(halt());
        Interpreter::new(program).execute().unwrap();
    }

    #[test]
    fn test_compiler_halt() {
        let program: Vec<Box<dyn Instruction>> = vec!(halt());
        assert!(Compiler::new().execute(program).unwrap().status.success());
    }

    #[test]
    fn test_interpreter_ran_off_end() {
        let program: &Vec<Box<dyn Instruction>> = &vec!(increment(0));
        let result = Interpreter::new(program).execute();

        assert_eq!(result.err(), Some(RanOffEnd))
    }

    #[test]
    fn test_interpreter_increment() {
        let program: &Vec<Box<dyn Instruction>> = &vec!(increment(0), increment(0), halt());
        let mut interpreter = Interpreter::new(program);

        interpreter.step().unwrap();
        assert_eq!(Ok(1), interpreter.register_read(0));

        interpreter.step().unwrap();
        assert_eq!(Ok(2), interpreter.register_read(0));

        assert_eq!((), interpreter.execute().unwrap());
    }

    #[test]
    fn test_interpreter_branch_equal() {
        let program: &Vec<Box<dyn Instruction>> = &vec!(increment(0),
                                                      increment(0),
                                                      increment(0),
                                                      increment(0),
                                                      increment(0),
                                                      increment(1),
                                                      branch_not_equal(0, 1, 5),
                                                      halt());
        Interpreter::new(program).execute().unwrap();
    }

    #[test]
    fn test_interpreter_push_pop() {
        let program: &Vec<Box<dyn Instruction>> = &vec!(increment(0), push(0),  // S: 1.
                                                        increment(0), push(0),  // S: 2, 1.
                                                        pop(1),  // S: 1.
                                                        halt());
        let mut interpreter = Interpreter::new(program);

        assert_eq!(0, interpreter.stack_size());
        assert_eq!(Err(StackEmpty), interpreter.stack_peek(0));

        interpreter.step_n(4).unwrap();

        assert_eq!(2, interpreter.stack_size());
        assert_eq!(2, interpreter.stack_peek(0).unwrap());
        assert_eq!(1, interpreter.stack_peek(1).unwrap());

        interpreter.step().unwrap();

        assert_eq!(1, interpreter.stack_size());
        assert_eq!(1, interpreter.stack_peek(0).unwrap());
        assert_eq!(2, interpreter.register_read(1).unwrap());

        interpreter.execute().unwrap();
    }
}

const REGISTERS_SIZE: usize = 32;
const STACK_SIZE: usize = 1024 * 1024;

type Registers = [i32; REGISTERS_SIZE];

mod instruction_set {
    use crate::{Instruction, HaltInstruction, IncrementInstruction, BranchNotEqualInstruction, PushInstruction, PopInstruction};

    pub fn branch_not_equal(test: usize, value: usize, jump: usize) -> Box<dyn Instruction>{
        Box::new(BranchNotEqualInstruction { test, value, jump })
    }

    pub fn halt() -> Box<dyn Instruction>{
        Box::new(HaltInstruction {})
    }

    pub fn increment(result: usize) -> Box<dyn Instruction>{
        Box::new(IncrementInstruction { result })
    }

    pub fn push(source: usize) -> Box<dyn Instruction>{
        Box::new(PushInstruction { source })
    }

    pub fn pop(result: usize) -> Box<dyn Instruction>{
        Box::new(PopInstruction { result })
    }
}

#[derive(Debug, PartialEq)]
pub enum Terminate {
    RanOffEnd, ProgramHalted, Unimplemented, StackEmpty, RegisterInvalid
}

pub trait Instruction : Debug {
    fn interpret(&self, interpreter: &mut Interpreter) -> Result<usize, Terminate>;
    fn compile(&self, compiler: &mut Compiler) -> Result<usize, Terminate>;
}

#[derive(Debug, Clone)]
pub struct Compiler {
    program: String
}

impl Compiler {
    fn new() -> Compiler {
        Compiler {
            program: String::new()
        }
    }

    fn execute(&mut self, program: Vec<Box<dyn Instruction>>) -> Result<Output, Terminate> {
        // FIXME: init can only be called once to init so just ignore errors.  Ultimately, this should be passed in.
        match simple_logger::init() { _ => {} }

        self.write_prologue();

        let length = program.len();

        for ipc  in 0..length {
            debug!("EMITTING IPC {}", ipc);

            let instruction = &*program[ipc];

            match instruction.compile(self) {
                Ok(_) => {},
                Err(err) => { return Err(err) }
            }
        }

        self.write_epilogue();

        fs::write("xmasvm.asm", &self.program).expect("Could not write asm file?");

        self.generate_executable();
        Ok(self.call_executable())
    }

    fn generate_executable(&self) {
        Command::new("nasm")
            .arg("-f").arg("elf32")
            .arg("xmasvm.asm")
            .arg("-o").arg("xmasvm.o")
            .output().expect("Could not execute nasm");

        Command::new("ld")
            .arg("-m").arg("elf_i386")
            .arg("xmasvm.o")
            .arg("-o").arg("xmasvm")
            .output().expect("Count not execute ld");
    }

    fn call_executable(&self) -> Output {
        let program = Command::new("./xmasvm").output().expect("Could not find xmasvm");
        program
    }

    fn write_prologue(&mut self) {
        self.program.push_str("global _start\n");
        self.program.push_str("section .text\n");
        self.program.push_str("_start:\n");
    }

    fn write_epilogue(&mut self) {
        self.program.push_str(";;;;; Pushed with xmasvm...ho ho ho\n");
    }
}

pub struct Interpreter<'a> {
    /// Instruction Pointer Counter - Which Instruction are we on in the program?
    ipc: usize,
    /// Stack pointer - Current index of where next stack element will be pushed
    sp: usize,
    /// All out potential registers
    registers: Registers,
    /// Stack
    stack: Vec<i32>,

    program: &'a Vec<Box<dyn Instruction>>
}

impl Interpreter<'_> {
    fn new<'a>(program: &'a Vec<Box<dyn Instruction>>) -> Interpreter {
        Interpreter {
            ipc: 0,
            sp: 0,
            registers: [0; REGISTERS_SIZE],
            stack: Vec::with_capacity(STACK_SIZE),
            program
        }
    }

    fn execute(&mut self) -> Result<(), Terminate> {
        // FIXME: init can only be called once to init so just ignore errors.  Ultimately, this should be passed in.
        match simple_logger::init() { _ => {} }

        loop {
            match self.step() {
                Ok(_) =>  {},
                Err(ProgramHalted) => { return Ok(()) } // better way?
                Err(err) => { return Err(err) }
            }
        }
    }

    /// Step returns () on successful step and Terminate when it cannot.
    fn step(&mut self) -> Result<(), Terminate> {
        if self.ipc >= self.program.len() { return Err(RanOffEnd); }

        let instruction = &*self.program[self.ipc];
        debug!("EXECUTING IPC {} = {:?}; SP: {}", self.ipc, instruction, self.sp);

        match instruction.interpret(self) {
            Ok(new_ipc) => {
                self.ipc = new_ipc;
                Ok(())
            },
            Err(err) => { return Err(err) }
        }
    }

    fn step_n(&mut self, count: usize) -> Result<(), Terminate> {
        for i in 0..count {
            if let Err(err) = self.step() {
                return Err(err)
            }
        }

        Ok(())
    }

    fn register_read(&self, register: usize) -> Result<i32, Terminate> {
        if register > REGISTERS_SIZE {
            Err(RegisterInvalid)
        } else {
            Ok(self.registers[register])
        }
    }

    fn stack_peek(&self, delta: i32) -> Result<i32, Terminate> {
        // FIXME: This will panic once we exceed i32 should Err(StackOverflow) instead
        let index: i32 = self.sp as i32 - delta - 1;

        if index < 0 {
            Err(StackEmpty)
        } else {
            Ok(*self.stack.get(index as usize).unwrap())
        }
    }

    fn stack_size(&self) -> usize {
        self.sp
    }
}

#[derive(Debug, Clone)]
struct HaltInstruction {}

impl Instruction for HaltInstruction {
    fn interpret(&self, _interpreter: &mut Interpreter) -> Result<usize, Terminate> {
        Err(ProgramHalted)
    }

    fn compile(&self, machine: &mut Compiler) -> Result<usize, Terminate> {
        machine.program.push_str("    mov eax, 1              ; exit()\n");
        machine.program.push_str("    mov ebx, 0              ; status = 0\n");
        machine.program.push_str("    int 0x80                ; call exit\n");
        Ok(0)
    }
}

#[derive(Debug, Clone)]
struct IncrementInstruction {
    result: usize
}

impl Instruction for IncrementInstruction {
    fn interpret(&self, mut machine: &mut Interpreter) -> Result<usize, Terminate> {
        let value = machine.registers[self.result];
        machine.registers[self.result] = value + 1;
        debug!("REGISTER {} is now {}", self.result, machine.registers[self.result]);
        Ok(machine.ipc + 1)
    }

    fn compile(&self, _machine: &mut Compiler) -> Result<usize, Terminate> {
        Err(Unimplemented)
    }
}

#[derive(Debug,Clone)]
struct BranchNotEqualInstruction {
    test: usize,
    value: usize,
    jump: usize
}

impl Instruction for BranchNotEqualInstruction {
    fn interpret(&self, machine: &mut Interpreter) -> Result<usize, Terminate> {
        let test = machine.registers[self.test];
        let value = machine.registers[self.value];
        if test != value {
            Ok(self.jump)
        } else {
            Ok(machine.ipc + 1)
        }
    }

    fn compile(&self, _machine: &mut Compiler) -> Result<usize, Terminate> {
        Err(Unimplemented)
    }
}

#[derive(Debug, Clone)]
struct AddInstruction {
    operand1: usize,
    operand2: usize,
    result: usize
}

impl Instruction for AddInstruction {
    fn interpret(&self, mut machine: &mut Interpreter) -> Result<usize, Terminate> {
        machine.registers[self.result] = machine.registers[self.operand1] + machine.registers[self.operand2];
        Ok(machine.ipc + 1)
    }

    fn compile(&self, _machine: &mut Compiler) -> Result<usize, Terminate> {
        Err(Unimplemented)
    }
}

#[derive(Debug, Clone)]
struct PushInstruction {
    source: usize
}

impl Instruction for PushInstruction {
    fn interpret(&self, mut machine: &mut Interpreter) -> Result<usize, Terminate> {
        machine.stack.push(machine.registers[self.source]);
        machine.sp += 1;
        Ok(machine.ipc + 1)
    }

    fn compile(&self, _machine: &mut Compiler) -> Result<usize, Terminate> {
        Err(Unimplemented)
    }
}

#[derive(Debug, Clone)]
struct PopInstruction {
    result: usize
}

impl Instruction for PopInstruction {
    fn interpret(&self, mut machine: &mut Interpreter) -> Result<usize, Terminate> {
        machine.registers[self.result] = machine.stack.pop().unwrap();
        machine.sp -= 1;
        Ok(machine.ipc + 1)
    }

    fn compile(&self, _machine: &mut Compiler) -> Result<usize, Terminate> {
        Err(Unimplemented)
    }
}