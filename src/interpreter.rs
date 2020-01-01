extern crate log;
extern crate simple_logger;
use log::debug;
use crate::{Registers, REGISTERS_SIZE, STACK_SIZE, Terminate};
use crate::instruction::Instruction;
use crate::operand::{Operand, Tag};

pub struct Interpreter<'a> {
    /// Instruction Pointer Counter - Which Instruction are we on in the program?
    pub(crate) ipc: usize,
    /// Stack pointer - Current index of where next stack element will be pushed
    pub(crate) sp: usize,
    /// All out potential registers
    registers: Registers,
    /// Stack
    pub(crate) stack: Vec<i32>,

    program: &'a Vec<Box<dyn Instruction>>
}

impl Interpreter<'_> {
    pub(crate) fn new<'a>(program: &'a Vec<Box<dyn Instruction>>) -> Interpreter {
        Interpreter {
            ipc: 0,
            sp: 0,
            registers: [0; REGISTERS_SIZE],
            stack: Vec::with_capacity(STACK_SIZE),
            program
        }
    }

    pub(crate) fn execute(&mut self) -> Result<(), Terminate> {
        // FIXME: init can only be called once to init so just ignore errors.  Ultimately, this should be passed in.
        match simple_logger::init() { _ => {} }

        loop {
            match self.step() {
                Ok(_) =>  {},
                Err(Terminate::ProgramHalted) => { return Ok(()) } // better way?
                Err(err) => { return Err(err) }
            }
        }
    }

    /// Step returns () on successful step and Terminate when it cannot.
    pub(crate) fn step(&mut self) -> Result<(), Terminate> {
        if self.ipc >= self.program.len() { return Err(Terminate::RanOffEnd); }

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

    pub(crate) fn step_n(&mut self, count: usize) -> Result<(), Terminate> {
        for _ in 0..count {
            if let Err(err) = self.step() {
                return Err(err)
            }
        }

        Ok(())
    }

    pub(crate) fn register_read(&self, register: usize) -> Result<i32, Terminate> {
        if register > REGISTERS_SIZE {
            Err(Terminate::RegisterInvalid)
        } else {
            Ok(self.registers[register])
        }
    }

    pub(crate) fn stack_peek(&self, delta: i32) -> Result<i32, Terminate> {
        // FIXME: This will panic once we exceed i32 should Err(StackOverflow) instead
        let index: i32 = self.sp as i32 - delta - 1;

        if index < 0 {
            Err(Terminate::StackEmpty)
        } else {
            Ok(*self.stack.get(index as usize).unwrap())
        }
    }

    pub(crate) fn stack_size(&self) -> usize {
        self.sp
    }

    pub(crate) fn value(&self, operand: &Operand) -> i32 {
        match operand.tag {
            Tag::Direct => { self.registers[operand.value as usize] },
            Tag::Indirect => { self.registers[self.registers[operand.value as usize] as usize] },
            Tag::Literal => { operand.value }
        }
    }

    pub(crate) fn store(&mut self, operand: &Operand, value: i32) -> Result<i32, Terminate> {
        match operand.tag {
            Tag::Direct => self.registers[operand.value as usize] = value,
            Tag::Indirect => self.registers[self.registers[operand.value as usize] as usize] = value,
            Tag::Literal => return Err(Terminate::RegisterInvalid)
        }

        Ok(value)
    }
}