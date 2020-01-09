extern crate log;
extern crate simple_logger;
use crate::instruction::Instruction;
use crate::operand::{Operand, Tag};
use crate::{Registers, Terminate, REGISTERS_SIZE, STACK_SIZE};
use log::debug;

pub struct Interpreter<'a> {
    /// Instruction Pointer Counter - Which Instruction are we on in the program?
    pub(crate) ipc: usize,
    /// Stack pointer - Current index of where next stack element will be pushed
    pub(crate) sp: usize,
    /// All out potential registers
    registers: Registers,
    /// Stack
    pub(crate) stack: Vec<i32>,
    /// List of instructions we are interpreting
    program: &'a [Box<dyn Instruction>],
}

impl Interpreter<'_> {
    pub(crate) fn new<'a>(program: &'a [Box<dyn Instruction>]) -> Interpreter {
        Interpreter {
            ipc: 0,
            sp: 0,
            registers: [0; REGISTERS_SIZE],
            stack: Vec::with_capacity(STACK_SIZE),
            program,
        }
    }

    /// Execute the program associated with this intepreter.
    /// Note: This is not restartable.  You can only call execute once.
    pub(crate) fn execute(&mut self) -> Result<(), Terminate> {
        // FIXME: init can only be called once to init so just ignore errors.  Ultimately, this should be passed in.
        match simple_logger::init() {
            _ => {}
        }

        loop {
            match self.step() {
                Ok(_) => {}
                Err(Terminate::ProgramHalted) => return Ok(()), // better way?
                Err(err) => return Err(err),
            }
        }
    }

    /// Step returns () on successful step and Terminate when it cannot.
    pub(crate) fn step(&mut self) -> Result<(), Terminate> {
        if self.ipc >= self.program.len() {
            return Err(Terminate::RanOffEnd);
        }

        let instruction = &*self.program[self.ipc];
        debug!(
            "EXECUTING IPC {} = {:?}; SP: {}",
            self.ipc, instruction, self.sp
        );

        match instruction.interpret(self) {
            Ok(new_ipc) => {
                self.ipc = new_ipc;
                Ok(())
            }
            Err(err) => Err(err)
        }
    }

    /// Execute n instructions before stopping
    pub(crate) fn step_n(&mut self, count: usize) -> Result<(), Terminate> {
        for _ in 0..count {
            if let Err(err) = self.step() {
                return Err(err);
            }
        }

        Ok(())
    }

    /// What is the contents of the register at location specified.
    pub(crate) fn register_read(&self, register: usize) -> Result<i32, Terminate> {
        if register > REGISTERS_SIZE {
            Err(Terminate::RegisterInvalid)
        } else {
            Ok(self.registers[register])
        }
    }

    /// What is at the current stack element or delta elements above/below the current stack
    /// element.
    pub(crate) fn stack_peek(&self, delta: i32) -> Result<i32, Terminate> {
        // FIXME: This will panic once we exceed i32 should Err(StackOverflow) instead
        let index: i32 = self.sp as i32 - delta - 1;

        if index < 0 {
            Err(Terminate::StackEmpty)
        } else {
            Ok(*self.stack.get(index as usize).unwrap())
        }
    }

    /// How many elements are currently pushed on the stack.
    pub(crate) fn stack_size(&self) -> usize {
        self.sp
    }

    /// What is the value associated with this operand.
    pub(crate) fn value(&self, operand: &Operand) -> i32 {
        match operand.tag {
            Tag::Direct => self.registers[operand.value as usize],
            Tag::Indirect => self.registers[self.registers[operand.value as usize] as usize],
            Tag::Literal => operand.value,
        }
    }

    /// Store value at the specified operand...or die tryin'.
    pub(crate) fn store(&mut self, operand: &Operand, value: i32) -> Result<i32, Terminate> {
        match operand.tag {
            Tag::Direct => self.registers[operand.value as usize] = value,
            Tag::Indirect => {
                self.registers[self.registers[operand.value as usize] as usize] = value
            }
            Tag::Literal => return Err(Terminate::RegisterInvalid),
        }

        Ok(value)
    }
}
