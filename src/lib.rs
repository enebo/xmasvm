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
    use crate::Tage::{Direct, Literal};

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
        let a = &Operand { tag: Direct, value: 0};
        let program: &Vec<Box<dyn Instruction>> = &vec!(increment(a));
        let result = Interpreter::new(program).execute();

        assert_eq!(result.err(), Some(RanOffEnd))
    }

    #[test]
    fn test_interpreter_increment() {
        let a = &Operand { tag: Direct, value: 0};
        let program: &Vec<Box<dyn Instruction>> = &vec!(increment(a), increment(a), halt());
        let mut interpreter = Interpreter::new(program);

        interpreter.step().unwrap();
        assert_eq!(1, interpreter.value(a));

        interpreter.step().unwrap();
        assert_eq!(2, interpreter.value(a));

        assert_eq!((), interpreter.execute().unwrap());
    }

    #[test]
    fn test_interpreter_add() {
        let a = &Operand { tag: Direct, value: 0};
        let five = &Operand { tag: Literal, value: 5};
        let one = &Operand { tag: Literal, value: 1};
        let program: &Vec<Box<dyn Instruction>> = &vec!(add(a, five, one), halt());
        let mut interpreter = Interpreter::new(program);

        interpreter.execute().unwrap();

        assert_eq!(6, interpreter.value(a));
    }

    #[test]
    fn test_interpreter_branch_equal() {
        let a = &Operand { tag: Direct, value: 0};
        let b = &Operand { tag: Direct, value: 1};
        let five = &Operand { tag: Literal, value: 5};
        let one = &Operand { tag: Literal, value: 1};
        let program: &Vec<Box<dyn Instruction>> = &vec!(store(a, five),
                                                        increment(b),
                                                        branch_not_equal(a, b, one),
                                                        halt());
        Interpreter::new(program).execute().unwrap();
    }

    #[test]
    fn test_interpreter_push_pop() {
        let a = &Operand { tag: Direct, value: 0};
        let b = &Operand { tag: Direct, value: 1};
        let program: &Vec<Box<dyn Instruction>> = &vec!(increment(a), push(a),  // S: 1.
                                                        increment(a), push(a),  // S: 2, 1.
                                                        pop(b),  // S: 1.
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
    use crate::{Instruction, HaltInstruction, IncrementInstruction, BranchNotEqualInstruction,
                PushInstruction, PopInstruction, Operand, StoreInstruction, AddInstruction};

    pub fn add(result: &'static Operand, operand1: &'static Operand, operand2: &'static Operand) -> Box<dyn Instruction>{
        Box::new(AddInstruction { result, operand1, operand2 })
    }

    pub fn branch_not_equal(test: &'static Operand, value: &'static Operand, jump: &'static Operand) -> Box<dyn Instruction>{
        Box::new(BranchNotEqualInstruction { test, value, jump })
    }

    pub fn halt() -> Box<dyn Instruction>{
        Box::new(HaltInstruction {})
    }

    pub fn increment(result: &'static Operand) -> Box<dyn Instruction>{
        Box::new(IncrementInstruction { result })
    }

    pub fn push(source: &'static Operand) -> Box<dyn Instruction>{
        Box::new(PushInstruction { source })
    }

    pub fn pop(result: &'static Operand) -> Box<dyn Instruction>{
        Box::new(PopInstruction { result })
    }

    pub fn store(result: &'static Operand, value: &'static Operand) -> Box<dyn Instruction>{
        Box::new(StoreInstruction { result, value })
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
pub enum Tage { Direct, Indirect, Literal }

#[derive(Debug, Clone)]
pub struct Operand {
    tag: Tage,
    value: i32
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
        for _ in 0..count {
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

    fn value(&self, operand: &Operand) -> i32 {
        match operand.tag {
            Tage::Direct => { self.registers[operand.value as usize] },
            Tage::Indirect => { self.registers[self.registers[operand.value as usize] as usize] },
            Tage::Literal => { operand.value }
        }
    }

    fn store(&mut self, operand: &Operand, value: i32) -> i32 {
        // FIXME: Should error is value is this or should we use Regster as a type of Operand
        match operand.tag {
            Tage::Direct => self.registers[operand.value as usize] = value,
            Tage::Indirect => self.registers[self.registers[operand.value as usize] as usize] = value,
            Tage::Literal => panic!("Store boom fix")
        }

        value
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
struct IncrementInstruction<'a> {
    result: &'a Operand
}

impl <'a> Instruction for IncrementInstruction<'a> {
    fn interpret(&self, machine: &mut Interpreter) -> Result<usize, Terminate> {
        let value = machine.value(&self.result);
        machine.store(&self.result, value + 1);
        debug!("REGISTER {:?} is now {}", self.result, machine.value(&self.result));
        Ok(machine.ipc + 1)
    }

    fn compile(&self, machine: &mut Compiler) -> Result<usize, Terminate> {
        machine.program.push_str("    inc ");
        // FIXME:
//        machine.program.push_str(machine.register_for(self.result));
        Ok(0)
    }
}

#[derive(Debug,Clone)]
struct BranchNotEqualInstruction<'a> {
    test: &'a Operand,
    value: &'a Operand,
    jump: &'a Operand
}

// FIXME: write test showing what happens is a Value is used for register but is bogus.
impl <'a> Instruction for BranchNotEqualInstruction<'a> {
    fn interpret(&self, machine: &mut Interpreter) -> Result<usize, Terminate> {
        let test = machine.value(&self.test);
        let value = machine.value(&self.value);
        if test != value {
            Ok(machine.value(&self.jump) as usize)
        } else {
            Ok(machine.ipc + 1)
        }
    }

    fn compile(&self, _machine: &mut Compiler) -> Result<usize, Terminate> {
        Err(Unimplemented)
    }
}

#[derive(Debug, Clone)]
struct AddInstruction<'a> {
    operand1: &'a Operand,
    operand2: &'a Operand,
    result: &'a Operand
}

impl <'a> Instruction for AddInstruction<'a>  {
    fn interpret(&self, machine: &mut Interpreter) -> Result<usize, Terminate> {
        let sum = machine.value(&self.operand1) + machine.value(&self.operand2);
        machine.store(&self.result, sum);
        Ok(machine.ipc + 1)
    }

    fn compile(&self, _machine: &mut Compiler) -> Result<usize, Terminate> {
        Err(Unimplemented)
    }
}

#[derive(Debug, Clone)]
struct PushInstruction<'a> {
    source: &'a Operand
}

impl <'a> Instruction for PushInstruction<'a> {
    fn interpret(&self, mut machine: &mut Interpreter) -> Result<usize, Terminate> {
        let value = machine.value(self.source);
        machine.stack.push(value);
        machine.sp += 1;
        Ok(machine.ipc + 1)
    }

    fn compile(&self, _machine: &mut Compiler) -> Result<usize, Terminate> {
        Err(Unimplemented)
    }
}

#[derive(Debug, Clone)]
struct PopInstruction<'a> {
    result: &'a Operand
}

impl <'a> Instruction for PopInstruction<'a> {
    fn interpret(&self, mut machine: &mut Interpreter) -> Result<usize, Terminate> {
        let value = machine.stack.pop().unwrap();
        machine.store(&self.result, value);
        machine.sp -= 1;
        Ok(machine.ipc + 1)
    }

    fn compile(&self, _machine: &mut Compiler) -> Result<usize, Terminate> {
        Err(Unimplemented)
    }
}

#[derive(Debug, Clone)]
struct StoreInstruction <'a> {
    result: &'a Operand,
    value: &'a Operand
}

impl <'a> Instruction for StoreInstruction<'a> {
    fn interpret(&self, machine: &mut Interpreter) -> Result<usize, Terminate> {
        let value = machine.value(self.value);
        machine.store(&self.result, value);
        Ok(machine.ipc + 1)
    }

    fn compile(&self, _compiler: &mut Compiler) -> Result<usize, Terminate> {
        Err(Unimplemented)
    }
}