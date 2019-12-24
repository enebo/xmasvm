extern crate log;
extern crate simple_logger;
use log::debug;
use crate::InterpreterInterrupt::{RanOffEnd, ProgramHalted};

#[cfg(test)]
mod tests {
    use super::*;
    use super::instruction_set::*;

    #[test]
    fn test_interpreter_halt() {
        let program: Vec<Box<dyn InterpretedInstruction>> = vec!(halt());
        Interpreter {}.execute(program).unwrap();
    }

    #[test]
    fn test_interpreter_ran_off_end() {
        let program: Vec<Box<dyn InterpretedInstruction>> = vec!(increment(0));
        let result = Interpreter {}.execute(program);

        assert_eq!(result.err(), Some(RanOffEnd))
    }

    #[test]
    fn test_interpreter_increment() {
        let program: Vec<Box<dyn InterpretedInstruction>> = vec!(increment(0), increment(0), halt());
        Interpreter {}.execute(program).unwrap();
    }

    #[test]
    fn test_interpreter_branch_equal() {
        let program: Vec<Box<dyn InterpretedInstruction>> = vec!(increment(0),
                                                                 increment(0),
                                                                 increment(0),
                                                                 increment(0),
                                                                 increment(0),
                                                                 increment(1),
                                                                 branch_not_equal(0, 1, 5),
                                                                 halt());
        Interpreter {}.execute(program).unwrap();
    }
}

const REGISTERS_SIZE: usize = 128;

type Registers = [usize; REGISTERS_SIZE];

mod instruction_set {
    use crate::{InterpretedInstruction, HaltInstruction, IncrementInstruction, BranchNotEqualInstruction};

    pub fn branch_not_equal(test: usize, value: usize, jump: usize) -> Box<dyn InterpretedInstruction>{
        Box::new(BranchNotEqualInstruction { test, value, jump })
    }

    pub fn halt() -> Box<dyn InterpretedInstruction>{
        Box::new(HaltInstruction {})
    }

    pub fn increment(register: usize) -> Box<dyn InterpretedInstruction>{
        Box::new(IncrementInstruction { result: register })
    }
}

#[derive(Debug, PartialEq)]
pub enum InterpreterInterrupt {
    RanOffEnd, ProgramHalted
}

pub trait InterpretedInstruction {
    fn interpret(&self, ipc: usize, registers: &mut Registers) -> Result<usize, InterpreterInterrupt>;
}

trait ProgramExecutor {
    fn execute(&self, program: Vec<Box<dyn InterpretedInstruction>>) -> Result<(), InterpreterInterrupt>;
}

#[derive(Debug, Clone)]
struct Interpreter {}

impl ProgramExecutor for Interpreter {
    fn execute(&self, program: Vec<Box<dyn InterpretedInstruction>>) -> Result<(), InterpreterInterrupt>{
        // FIXME: init can only be called once to init so just ignore errors.  Ultimately, this should be passed in.
        match simple_logger::init() { _ => {} }
        let mut ipc: usize = 0;
        let mut registers: Registers = [0; REGISTERS_SIZE];

        loop {
            debug!("EXECUTING IPC {}", ipc);
            if ipc >= program.len() { return Err(RanOffEnd); }

            match program[ipc].interpret(ipc, &mut registers) {
                Ok(new_ipc) => { ipc = new_ipc },
                Err(ProgramHalted) => { return Ok(()) } // better way?
                Err(err) => { return Err(err) }
            }
        }
    }
}

#[derive(Debug, Clone)]
struct HaltInstruction {}

impl InterpretedInstruction for HaltInstruction {
    fn interpret(&self, _ipc: usize, mut _registers: &mut Registers) -> Result<usize, InterpreterInterrupt> {
        Err(ProgramHalted)
    }
}

#[derive(Debug, Clone)]
struct IncrementInstruction {
    result: usize
}

impl InterpretedInstruction for IncrementInstruction {
    fn interpret(&self, ipc: usize, registers: &mut Registers) -> Result<usize, InterpreterInterrupt> {
        let value = registers[self.result];
        registers[self.result] = value + 1;
        debug!("REGISTER {} is now {}", self.result, registers[self.result]);
        Ok(ipc + 1)
    }
}

#[derive(Debug,Clone)]
struct BranchNotEqualInstruction {
    test: usize,
    value: usize,
    jump: usize
}

impl InterpretedInstruction for BranchNotEqualInstruction {
    fn interpret(&self, ipc: usize, registers: &mut Registers) -> Result<usize, InterpreterInterrupt> {
        let test = registers[self.test];
        let value = registers[self.value];
        if test != value {
            Ok(self.jump)
        } else {
            Ok(ipc + 1)
        }
    }
}

#[derive(Debug, Clone)]
struct AddInstruction {
    operand1: usize,
    operand2: usize,
    result: usize
}

impl InterpretedInstruction for AddInstruction {
    fn interpret(&self, ipc: usize, registers: &mut Registers) -> Result<usize, InterpreterInterrupt> {
        registers[self.result] = registers[self.operand1] + registers[self.operand2];
        Ok(ipc + 1)
    }
}