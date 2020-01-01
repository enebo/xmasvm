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
    use crate::Tag::{Direct, Literal};

    #[test]
    fn test_interpreter_halt() {
        let program: &Vec<Box<dyn Instruction>> = &vec!(halt());
        Interpreter::new(program).execute().unwrap();
    }

    #[test]
    fn test_compiler_halt() {
        let program: &Vec<Box<dyn Instruction>> = &vec!(halt());
        assert!(Compiler::new(program).execute().unwrap().status.success());
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
        let b = &Operand { tag: Direct, value: 0};
        let program: &Vec<Box<dyn Instruction>> = &vec!(increment(b), increment(b), halt());
        let mut interpreter = Interpreter::new(program);

        interpreter.step().unwrap();
        assert_eq!(1, interpreter.value(b));

        interpreter.step().unwrap();
        assert_eq!(2, interpreter.value(b));

        assert_eq!((), interpreter.execute().unwrap());
    }

    #[test]
    fn test_compiler_increment() {
        let b = &Operand { tag: Direct, value: 1};
        let program: &Vec<Box<dyn Instruction>> = &vec!(increment(b), increment(b), halt());
        let mut compiler = Compiler::new(program);

        assert_eq!(2, compiler.execute().unwrap().status.code().unwrap());
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
    fn test_compiler_add() {
        let b = &Operand { tag: Direct, value: 1};
        let five = &Operand { tag: Literal, value: 5};
        let one = &Operand { tag: Literal, value: 1};
        let program: &Vec<Box<dyn Instruction>> = &vec!(add(b, five, one), halt());
        let mut compiler = Compiler::new(program);

        assert_eq!(6, compiler.execute().unwrap().status.code().unwrap());
    }

    #[test]
    fn test_compiler_add_no_mov() {
        let b = &Operand { tag: Direct, value: 1};
        let five = &Operand { tag: Literal, value: 5};
        let program: &Vec<Box<dyn Instruction>> = &vec!(add(b, b, five), halt());
        let mut compiler = Compiler::new(program);

        assert_eq!(5, compiler.execute().unwrap().status.code().unwrap());
    }

    #[test]
    fn test_interpreter_branch_not_equal() {
        let a = &Operand { tag: Direct, value: 0};
        let b = &Operand { tag: Direct, value: 1};
        let five = &Operand { tag: Literal, value: 5};
        let program: &Vec<Box<dyn Instruction>> = &vec!(store(a, five),
                                                        increment(b),
                                                        branch_not_equal(a, b, 1),
                                                        halt());
        Interpreter::new(program).execute().unwrap();
    }

    #[test]
    fn test_compiler_branch_not_equal() {
        let a = &Operand { tag: Direct, value: 0};
        let b = &Operand { tag: Direct, value: 1};
        // Jump past second increment so halt reports 1 instead of 2.
        let program: &Vec<Box<dyn Instruction>> = &vec!(increment(b),
                                                        branch_not_equal(a, b, 3),
                                                        increment(b),
                                                        halt());
        let mut compiler = Compiler::new(program);

        assert_eq!(1, compiler.execute().unwrap().status.code().unwrap());
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

    pub fn branch_not_equal(test: &'static Operand, value: &'static Operand, jump: usize) -> Box<dyn Instruction>{
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

pub trait Instruction : Debug + ToString {
    fn interpret(&self, interpreter: &mut Interpreter) -> Result<usize, Terminate>;
    fn compile(&self, compiler: &mut Compiler) -> Result<usize, Terminate>;
    fn jump_location(&self) -> Option<usize> {
        None
    }
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub enum Tag { Direct, Indirect, Literal }

#[derive(Debug, Clone)]
pub struct Operand {
    tag: Tag,
    value: i32
}

impl ToString for Operand {
    fn to_string(&self) -> String {
        format!("{}{}",
                match self.tag {
                    Tag::Direct=> 'd',
                    Tag::Indirect => 'i',
                    Tag::Literal => 'l'
                },
                self.value.to_string())
    }
}

#[derive(Debug, Clone)]
pub struct Compiler<'a> {
    program: &'a Vec<Box<dyn Instruction>>,
    output: String
}

macro_rules! addi_expand {
    ($instr:expr, $str:expr, ($arg:expr,)) => {{
        $str.push_str($arg);
        $str.push_str("\t\t\t\t; ");
        $str.push_str(&$instr.to_string());
        $str.push('\n');
    }};

    ($instr:expr, $str:expr, ($arg:expr, $($rest:expr,)*)) => {{
        $str.push_str($arg);
        $str.push_str(", ");
        addi_expand!($instr, $str, ($($rest,)*))
    }};
}

macro_rules! addi {
    ($instr:expr, $machine:expr, $opcode:expr, $($e:expr),*) => {{
        $machine.output.push_str("    ");
        $machine.output.push_str($opcode);
        $machine.output.push(' ');
        addi_expand!($instr, $machine.output, ($($e,)*))
    }}
}

/// Compiler targetting x86(32) nasm.
///
/// The instruction set was pretty arbitrarily chosen and intentionally not exactly
/// x86.  As such there needs to be some mappings.  For example, register 0 will end
/// up mapping to eax.  If for some reason an x86 instr ends up putting something into
/// eax then it may wipe out our original user of register 0.
impl Compiler<'_> {
    fn new<'a>(program: &'a Vec<Box<dyn Instruction>>) -> Compiler {
        Compiler {
            program: program,
            /// Input to be written out for 'nasm' to assemble.
            output: String::new()
        }
    }

    /// Walk all instructions and mark up a list of where labels should be created
    fn calculate_labels(&self) -> Vec<usize> {
        let length = self.program.len();
        let mut labels: Vec<usize> = vec![0; length];

        for i in 0..length {
            let instruction = &*self.program[i];

            if let Some(jump_location) = instruction.jump_location() {
                labels[jump_location] = i;
            }
        }

        labels
    }

    fn call_executable(&self) -> Output {
        let program = Command::new("./xmasvm").output().expect("Could not find xmasvm");
        program
    }

    fn execute(&mut self) -> Result<Output, Terminate> {
        // FIXME: init can only be called once to init so just ignore errors.  Ultimately, this should be passed in.
        match simple_logger::init() { _ => {} }

        let labels = self.calculate_labels();

        self.write_prologue();

        let length = self.program.len();

        for ipc  in 0..length {
            debug!("EMITTING IPC {}", ipc);

            let instruction = &*self.program[ipc];

            if labels[ipc] != 0 {
                self.output.push_str("\n_");
                self.output.push_str(ipc.to_string().as_ref());
                self.output.push_str(":\n");
            }

            match instruction.compile(self) {
                Ok(_) => {},
                Err(err) => { return Err(err) }
            }
        }

        self.write_epilogue();

        debug!("NASM OUTPUT:\n{}", self.output);

        fs::write("xmasvm.asm", &self.output).expect("Could not write asm file?");

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

    fn native_register_for(&self, operand: &Operand) -> Result<String, Terminate> {
        if operand.tag == Tag::Literal { return Err(RegisterInvalid) }

        match (operand.value, operand.tag) {
            (0, Tag::Direct) => { Ok("eax".parse().unwrap()) },
            (0, Tag::Indirect) => { Ok("[eax]".parse().unwrap()) },
            (1, Tag::Direct) => { Ok("ebx".parse().unwrap()) },
            (1, Tag::Indirect) => { Ok("[ebx]".parse().unwrap()) },
            _ => { Err(RegisterInvalid)}
        }
    }

    fn native_register_or_value(&self, operand: &Operand) -> Result<String, Terminate> {
        let register = self.native_register_for(operand);

        match register {
            Err(RegisterInvalid) if operand.tag == Tag::Literal =>  { Ok(operand.value.to_string()) },
            _ => { register }
        }
    }

    // FIXME: Allow optional comment as parameter

    fn write_prologue(&mut self) {
        self.output.push_str("global _start\n");
        self.output.push_str("section .text\n");
        self.output.push_str("_start:\n");
    }

    fn write_epilogue(&mut self) {
        self.output.push_str(";;;;; Pushed with xmasvm...ho ho ho\n");
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
            Tag::Direct => { self.registers[operand.value as usize] },
            Tag::Indirect => { self.registers[self.registers[operand.value as usize] as usize] },
            Tag::Literal => { operand.value }
        }
    }

    fn store(&mut self, operand: &Operand, value: i32) -> i32 {
        // FIXME: Should error is value is this or should we use Regster as a type of Operand
        match operand.tag {
            Tag::Direct => self.registers[operand.value as usize] = value,
            Tag::Indirect => self.registers[self.registers[operand.value as usize] as usize] = value,
            Tag::Literal => panic!("Store boom fix")
        }

        value
    }

}

#[derive(Debug, Clone)]
struct HaltInstruction {}

impl ToString for HaltInstruction {
    fn to_string(&self) -> String {
        "Halt".parse().unwrap()
    }
}

impl Instruction for HaltInstruction {
    fn interpret(&self, _interpreter: &mut Interpreter) -> Result<usize, Terminate> {
        Err(ProgramHalted)
    }

    fn compile(&self, machine: &mut Compiler) -> Result<usize, Terminate> {
        addi!(self, machine, "mov", "eax", "1");
        addi!(self, machine, "int", "0x80");
        Ok(0)
    }
}

#[derive(Debug, Clone)]
struct IncrementInstruction<'a> {
    result: &'a Operand
}

impl <'a> ToString for IncrementInstruction<'a> {
    fn to_string(&self) -> String {
        format!("Increment result: {}", self.result.to_string())
    }
}

// FIXME: Add tests for using literals where registers expected for both interp and compiler
impl <'a> Instruction for IncrementInstruction<'a> {
    fn interpret(&self, machine: &mut Interpreter) -> Result<usize, Terminate> {
        let value = machine.value(&self.result);
        machine.store(&self.result, value + 1);
        debug!("REGISTER {:?} is now {}", self.result, machine.value(&self.result));
        Ok(machine.ipc + 1)
    }

    fn compile(&self, machine: &mut Compiler) -> Result<usize, Terminate> {
        let register = machine.native_register_for(self.result).unwrap();
        addi!(self, machine, "inc", register.as_str());
        Ok(0)
    }
}

#[derive(Debug,Clone)]
struct BranchNotEqualInstruction<'a> {
    test: &'a Operand,
    value: &'a Operand,
    jump: usize
}

impl <'a> ToString for BranchNotEqualInstruction<'a> {
    fn to_string(&self) -> String {
        format!("BranchNotEqual test: {} value: {}, jump: {}",
                self.test.to_string(),
                self.value.to_string(),
                self.jump.to_string())
    }
}

// FIXME: write test showing what happens is a Value is used for register but is bogus.
impl <'a> Instruction for BranchNotEqualInstruction<'a> {
    fn interpret(&self, machine: &mut Interpreter) -> Result<usize, Terminate> {
        let test = machine.value(&self.test);
        let value = machine.value(&self.value);
        if test != value {
            Ok(self.jump)
        } else {
            Ok(machine.ipc + 1)
        }
    }

    fn compile(&self, machine: &mut Compiler) -> Result<usize, Terminate> {
        let test = machine.native_register_or_value(&self.test).unwrap();
        let value = machine.native_register_or_value(&self.value).unwrap();
        let mut jump_string = String::new();

        jump_string.push('_');
        jump_string.push_str(self.jump.to_string().as_str());

        addi!(self, machine, "cmp", test.as_str(), value.as_str());
        addi!(self, machine, "jne", jump_string.as_str());

        Ok(0)
    }

    // FIXME: jump should become non-operandd?
    fn jump_location(&self) -> Option<usize> {
        Some(self.jump)
    }
}

#[derive(Debug, Clone)]
struct AddInstruction<'a> {
    operand1: &'a Operand,
    operand2: &'a Operand,
    result: &'a Operand
}

impl <'a> ToString for AddInstruction<'a> {
    fn to_string(&self) -> String {
        format!("Add result: {}, operand1: {}, operand2 {}",
            self.result.to_string(),
            self.operand1.to_string(),
            self.operand2.to_string())
    }
}

impl <'a> Instruction for AddInstruction<'a>  {
    fn interpret(&self, machine: &mut Interpreter) -> Result<usize, Terminate> {
        let sum = machine.value(&self.operand1) + machine.value(&self.operand2);
        machine.store(&self.result, sum);
        Ok(machine.ipc + 1)
    }

    fn compile(&self, machine: &mut Compiler) -> Result<usize, Terminate> {
        let result = machine.native_register_for(self.result).unwrap();
        let operand1 = machine.native_register_or_value(self.operand1).unwrap();
        let operand2 = machine.native_register_or_value(self.operand2).unwrap();

        if result != operand1 {
            addi!(self, machine, "mov", result.as_str(), operand1.as_str());
        }
        addi!(self, machine, "add", result.as_str(), operand2.as_str());
        Ok(0)
    }
}

#[derive(Debug, Clone)]
struct PushInstruction<'a> {
    source: &'a Operand
}

impl <'a> ToString for PushInstruction<'a> {
    fn to_string(&self) -> String {
        format!("Push source: {}", self.source.to_string())
    }
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

impl <'a> ToString for PopInstruction<'a> {
    fn to_string(&self) -> String {
        format!("Pop result: {}", self.result.to_string())
    }
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

impl <'a> ToString for StoreInstruction<'a> {
    fn to_string(&self) -> String {
        format!("Store result: {}, value: {}",
            self.result.to_string(),
            self.value.to_string(),
        )
    }
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