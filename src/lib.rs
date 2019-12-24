extern crate log;
extern crate simple_logger;
use log::debug;
use crate::Terminate::{RanOffEnd, ProgramHalted};

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
    use crate::{Instruction, HaltInstruction, IncrementInstruction, BranchNotEqualInstruction};

    pub fn branch_not_equal(test: usize, value: usize, jump: usize) -> Box<dyn Instruction>{
        Box::new(BranchNotEqualInstruction { test, value, jump })
    }

    pub fn halt() -> Box<dyn Instruction>{
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
    fn process(&self, machine: Machine) -> Result<usize, Terminate>;
}

pub trait ProgramExecutor<Machine=Self> {
    fn execute(&mut self, program: Vec<Box<dyn Instruction<Machine>>>) -> Result<(), Terminate>;
}

#[derive(Debug, Clone)]
pub struct Compiler {
}

impl ProgramExecutor for Compiler {
    fn execute(&mut self, program: Vec<Box<dyn Instruction<Compiler>>>) -> Result<(), Terminate> {
        // FIXME: init can only be called once to init so just ignore errors.  Ultimately, this should be passed in.
        match simple_logger::init() { _ => {} }

        let mut ipc = 0;

        loop {
            debug!("EXECUTING IPC {}", ipc);
            if ipc >= program.len() { return Ok(()); }

            match program[ipc].process(self.to_owned()) {
                Ok(_) => { ipc += 1 },
                Err(err) => { return Err(err) }
            }
        }
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

            match program[self.ipc].process(self.to_owned()) {
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
    fn process(&self, _machine: Interpreter) -> Result<usize, Terminate> {
        Err(ProgramHalted)
    }
}

impl Instruction<Compiler> for HaltInstruction {
    fn process(&self, _machine: Compiler) -> Result<usize, Terminate> {
        Err(ProgramHalted)
    }
}

#[derive(Debug, Clone)]
struct IncrementInstruction {
    result: usize
}

impl Instruction<Interpreter> for IncrementInstruction {
    fn process(&self, mut machine: Interpreter) -> Result<usize, Terminate> {
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
    fn process(&self, machine: Interpreter) -> Result<usize, Terminate> {
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
    fn process(&self, mut machine: Interpreter) -> Result<usize, Terminate> {
        machine.registers[self.result] = machine.registers[self.operand1] + machine.registers[self.operand2];
        Ok(machine.ipc + 1)
    }
}