
// https://play.rust-lang.org/?version=stable&mode=debug&edition=2015&gist=b38c87957a2f0194d030cf5424a84a49

extern crate log;
extern crate simple_logger;
use log::debug;
use crate::Terminate::{RanOffEnd, ProgramHalted, Unimplemented, StackEmpty};
use std::fs;

#[cfg(test)]
mod tests {
    use super::*;
    use super::instruction_set::*;

    #[test]
    fn test_interpreter_halt() {
        let program: Vec<Box<dyn Instruction>> = vec!(halt());
        Interpreter::new().execute(program).unwrap();
    }

    #[test]
    fn test_compiler_halt() {
        let program: Vec<Box<dyn Instruction>> = vec!(halt());
        Compiler::new().execute(program).unwrap();
    }

    #[test]
    fn test_interpreter_ran_off_end() {
        let program: Vec<Box<dyn Instruction>> = vec!(increment(0));
        let result = Interpreter::new().execute(program);

        assert_eq!(result.err(), Some(RanOffEnd))
    }

    #[test]
    fn test_interpreter_increment() {
        let program: Vec<Box<dyn Instruction>> = vec!(increment(0), increment(0), halt());
        Interpreter::new().execute(program).unwrap();
    }

    #[test]
    fn test_interpreter_branch_equal() {
        let program: Vec<Box<dyn Instruction>> = vec!(increment(0),
                                                      increment(0),
                                                      increment(0),
                                                      increment(0),
                                                      increment(0),
                                                      increment(1),
                                                      branch_not_equal(0, 1, 5),
                                                      halt());
        Interpreter::new().execute(program).unwrap();
    }

    #[test]
    fn test_interpreter_push() {
        let program: Vec<Box<dyn Instruction>> = vec!(increment(0), push(0), halt());
        let mut interpreter = Interpreter::new();

        interpreter.execute(program).unwrap();

        assert_eq!(1, interpreter.stack_peek().unwrap());
    }

    #[test]
    fn test_interpreter_stack_empty() {
        let program: Vec<Box<dyn Instruction>> = vec!(halt());
        let mut interpreter = Interpreter::new();

        interpreter.execute(program).unwrap();

        assert_eq!(Err(StackEmpty), interpreter.stack_peek());
    }
}

const REGISTERS_SIZE: usize = 32;
const STACK_SIZE: usize = 1024 * 1024;

type Registers = [i32; REGISTERS_SIZE];

mod instruction_set {
    use crate::{Instruction, HaltInstruction, IncrementInstruction, BranchNotEqualInstruction, PushInstruction};

    pub fn branch_not_equal(test: usize, value: usize, jump: usize) -> Box<dyn Instruction>{
        Box::new(BranchNotEqualInstruction { test, value, jump })
    }

    pub fn halt() -> Box<dyn Instruction>{
        Box::new(HaltInstruction {})
    }

    pub fn increment(register: usize) -> Box<dyn Instruction>{
        Box::new(IncrementInstruction { result: register })
    }

    pub fn push(source: usize) -> Box<dyn Instruction>{
        Box::new(PushInstruction { source })
    }
}

#[derive(Debug, PartialEq)]
pub enum Terminate {
    RanOffEnd, ProgramHalted, Unimplemented, StackEmpty
}

pub trait Instruction {
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

    fn execute(&mut self, program: Vec<Box<dyn Instruction>>) -> Result<(), Terminate> {
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

        Ok(())
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

#[derive(Debug, Clone)]
pub struct Interpreter {
    /// Instruction Pointer Counter - Which Instruction are we on in the program?
    ipc: usize,
    /// Stack pointer - Current index of where next stack element will be pushed
    sp: usize,
    /// All out potential registers
    registers: Registers,
    /// Stack
    stack: Vec<i32>
}

impl Interpreter {
    fn new() -> Interpreter {
        Interpreter {
            ipc: 0,
            sp: 0,
            registers: [0; REGISTERS_SIZE],
            stack: Vec::with_capacity(STACK_SIZE)
        }
    }

    fn execute(&mut self, program: Vec<Box<dyn Instruction>>) -> Result<(), Terminate> {
        // FIXME: init can only be called once to init so just ignore errors.  Ultimately, this should be passed in.
        match simple_logger::init() { _ => {} }

        loop {
            debug!("EXECUTING IPC {}", self.ipc);
            if self.ipc >= program.len() { return Err(RanOffEnd); }

            let instruction = &*program[self.ipc];

            match instruction.interpret(self) {
                Ok(new_ipc) => { self.ipc = new_ipc },
                Err(ProgramHalted) => { return Ok(()) } // better way?
                Err(err) => { return Err(err) }
            }
        }
    }

    fn stack_peek(&self) -> Result<i32, Terminate> {
        // FIXME: This will panic once we exceed i32 should Err instead
        if self.sp == 0 {
            Err(StackEmpty)
        } else {
            Ok(*self.stack.get(self.sp - 1).unwrap())
        }
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