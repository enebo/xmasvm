extern crate log;
extern crate simple_logger;
use log::debug;
use crate::Terminate::{RanOffEnd, ProgramHalted};
use std::fs;
use std::borrow::BorrowMut;

#[cfg(test)]
mod tests {
    use super::*;
    use super::instruction_set::*;

    #[test]
    fn test_interpreter_halt() {
        let program: Vec<Box<dyn Instruction<Interpreter>>> = vec!(halt());
        Interpreter::new().execute(program).unwrap();
    }

    #[test]
    fn test_compiler_halt() {
        let program: Vec<Box<dyn Instruction<Compiler>>> = vec!(haltc());
        Compiler::new().execute(program).unwrap();
    }

    #[test]
    fn test_interpreter_ran_off_end() {
        let program: Vec<Box<dyn Instruction<Interpreter>>> = vec!(increment(0));
        let result = Interpreter::new().execute(program);

        assert_eq!(result.err(), Some(RanOffEnd))
    }

    #[test]
    fn test_interpreter_increment() {
        let program: Vec<Box<dyn Instruction<Interpreter>>> = vec!(increment(0), increment(0), halt());
        Interpreter::new().execute(program).unwrap();
    }

    #[test]
    fn test_interpreter_branch_equal() {
        let program: Vec<Box<dyn Instruction<Interpreter>>> = vec!(increment(0),
                                                      increment(0),
                                                      increment(0),
                                                      increment(0),
                                                      increment(0),
                                                      increment(1),
                                                      branch_not_equal(0, 1, 5),
                                                      halt());
        Interpreter::new().execute(program).unwrap();
    }
}

const REGISTERS_SIZE: usize = 32;

type Registers = [usize; REGISTERS_SIZE];

mod instruction_set {
    use crate::{Instruction, HaltInstruction, IncrementInstruction, BranchNotEqualInstruction, Compiler};

    pub fn branch_not_equal(test: usize, value: usize, jump: usize) -> Box<dyn Instruction>{
        Box::new(BranchNotEqualInstruction { test, value, jump })
    }

    pub fn halt() -> Box<dyn Instruction>{
        Box::new(HaltInstruction {})
    }

    pub fn haltc() -> Box<dyn Instruction<Compiler>>{
        Box::new(HaltInstruction {})
    }

    pub fn increment(register: usize) -> Box<dyn Instruction>{
        Box::new(IncrementInstruction { result: register })
    }
}

#[derive(Debug, PartialEq)]
pub enum Terminate {
    RanOffEnd, ProgramHalted
}

pub trait Instruction<Machine=Interpreter> {
    fn process(&self, machine: &mut Machine) -> Result<usize, Terminate>;
}

pub trait ProgramExecutor<Machine=Self> {
    fn execute(&mut self, program: Vec<Box<dyn Instruction<Machine>>>) -> Result<(), Terminate>;
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

    fn write_prologue(&mut self) {
        self.program.push_str("global _start\n");
        self.program.push_str("section .text\n");
        self.program.push_str("_start:\n");
    }

    fn write_epilogue(&mut self) {
        self.program.push_str(";;;;; Pushed with xmasvm...ho ho ho\n");
    }
}

impl ProgramExecutor for Compiler {
    fn execute(&mut self, program: Vec<Box<dyn Instruction<Compiler>>>) -> Result<(), Terminate> {
        // FIXME: init can only be called once to init so just ignore errors.  Ultimately, this should be passed in.
        match simple_logger::init() { _ => {} }

        self.write_prologue();

        let length = program.len();

        for ipc  in 0..length {
            debug!("EMITTING IPC {}", ipc);

            match program[ipc].process(self) {
                Ok(_) => {},
                Err(err) => { return Err(err) }
            }
        }

        self.write_epilogue();

        fs::write("xmasvm.asm", &self.program).expect("Could not write asm file?");

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct Interpreter {
    ipc: usize,
    registers: Registers
}

impl Interpreter {
    fn new() -> Interpreter {
        Interpreter {
            ipc: 0,
            registers: [0; REGISTERS_SIZE]
        }
    }
}

impl ProgramExecutor for Interpreter {
    fn execute(&mut self, program: Vec<Box<dyn Instruction<Interpreter>>>) -> Result<(), Terminate> {
        // FIXME: init can only be called once to init so just ignore errors.  Ultimately, this should be passed in.
        match simple_logger::init() { _ => {} }

        loop {
            debug!("EXECUTING IPC {}", self.ipc);
            if self.ipc >= program.len() { return Err(RanOffEnd); }

            match program[self.ipc].process(self) {
                Ok(new_ipc) => { self.ipc = new_ipc },
                Err(ProgramHalted) => { return Ok(()) } // better way?
                Err(err) => { return Err(err) }
            }
        }
    }
}

#[derive(Debug, Clone)]
struct HaltInstruction {}

impl Instruction<Interpreter> for HaltInstruction {
    fn process(&self, _machine: &mut Interpreter) -> Result<usize, Terminate> {
        Err(ProgramHalted)
    }
}

impl Instruction<Compiler> for HaltInstruction {
    fn process(&self, machine: &mut Compiler) -> Result<usize, Terminate> {
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

impl Instruction<Interpreter> for IncrementInstruction {
    fn process(&self, mut machine: &mut Interpreter) -> Result<usize, Terminate> {
        let value = machine.registers[self.result];
        machine.registers[self.result] = value + 1;
        debug!("REGISTER {} is now {}", self.result, machine.registers[self.result]);
        Ok(machine.ipc + 1)
    }
}

#[derive(Debug,Clone)]
struct BranchNotEqualInstruction {
    test: usize,
    value: usize,
    jump: usize
}

impl Instruction<Interpreter> for BranchNotEqualInstruction {
    fn process(&self, machine: &mut Interpreter) -> Result<usize, Terminate> {
        let test = machine.registers[self.test];
        let value = machine.registers[self.value];
        if test != value {
            Ok(self.jump)
        } else {
            Ok(machine.ipc + 1)
        }
    }
}

#[derive(Debug, Clone)]
struct AddInstruction {
    operand1: usize,
    operand2: usize,
    result: usize
}

impl Instruction<Interpreter> for AddInstruction {
    fn process(&self, mut machine: &mut Interpreter) -> Result<usize, Terminate> {
        machine.registers[self.result] = machine.registers[self.operand1] + machine.registers[self.operand2];
        Ok(machine.ipc + 1)
    }
}