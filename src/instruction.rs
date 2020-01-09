extern crate log;
extern crate simple_logger;
use crate::compiler::Compiler;
use crate::interpreter::Interpreter;
use crate::operand::Operand;
use crate::Terminate;
use log::debug;
use std::fmt::Debug;

pub(crate) mod instruction_set {
    use crate::instruction::{
        AddInstruction, BranchNotEqualInstruction, HaltInstruction, IncrementInstruction,
        Instruction, PopInstruction, PushInstruction, StoreInstruction,
    };
    use crate::operand::Operand;

    pub fn add(
        result: &'static Operand,
        operand1: &'static Operand,
        operand2: &'static Operand,
    ) -> Box<dyn Instruction> {
        Box::new(AddInstruction {
            result,
            operand1,
            operand2,
        })
    }

    pub fn branch_not_equal(
        test: &'static Operand,
        value: &'static Operand,
        jump: usize,
    ) -> Box<dyn Instruction> {
        Box::new(BranchNotEqualInstruction { test, value, jump })
    }

    pub fn halt() -> Box<dyn Instruction> {
        Box::new(HaltInstruction {})
    }

    pub fn increment(result: &'static Operand) -> Box<dyn Instruction> {
        Box::new(IncrementInstruction { result })
    }

    pub fn push(source: &'static Operand) -> Box<dyn Instruction> {
        Box::new(PushInstruction { source })
    }

    pub fn pop(result: &'static Operand) -> Box<dyn Instruction> {
        Box::new(PopInstruction { result })
    }

    pub fn store(result: &'static Operand, value: &'static Operand) -> Box<dyn Instruction> {
        Box::new(StoreInstruction { result, value })
    }
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

pub trait Instruction: Debug + ToString {
    /// interpret this instruction
    fn interpret(&self, interpreter: &mut Interpreter) -> Result<usize, Terminate>;
    /// compile/translate this instruction to x86 nasm assembly
    fn compile(&self, compiler: &mut Compiler) -> Result<usize, Terminate>;
    /// This instruction may jump...but where?  For label generation in the compiler.
    fn jump_location(&self) -> Option<usize> {
        None
    }
}

#[derive(Debug, Clone)]
struct HaltInstruction {}

impl ToString for HaltInstruction {
    fn to_string(&self) -> String {
        "Halt".to_string()
    }
}

impl Instruction for HaltInstruction {
    fn interpret(&self, _interpreter: &mut Interpreter) -> Result<usize, Terminate> {
        Err(Terminate::ProgramHalted)
    }

    fn compile(&self, machine: &mut Compiler) -> Result<usize, Terminate> {
        addi!(self, machine, "mov", "eax", "1");
        addi!(self, machine, "int", "0x80");
        Ok(0)
    }
}

#[derive(Debug, Clone)]
struct IncrementInstruction<'a> {
    result: &'a Operand,
}

impl<'a> ToString for IncrementInstruction<'a> {
    fn to_string(&self) -> String {
        format!("Increment result: {}", self.result.to_string())
    }
}

impl<'a> Instruction for IncrementInstruction<'a> {
    fn interpret(&self, machine: &mut Interpreter) -> Result<usize, Terminate> {
        let value = machine.value(&self.result);
        machine.store(&self.result, value + 1)?;
        debug!(
            "REGISTER {:?} is now {}",
            self.result,
            machine.value(&self.result)
        );
        Ok(machine.ipc + 1)
    }

    fn compile(&self, machine: &mut Compiler) -> Result<usize, Terminate> {
        let register = machine.native_register_for(self.result).unwrap();
        addi!(self, machine, "inc", register.as_str());
        Ok(0)
    }
}

#[derive(Debug, Clone)]
struct BranchNotEqualInstruction<'a> {
    test: &'a Operand,
    value: &'a Operand,
    jump: usize,
}

impl<'a> ToString for BranchNotEqualInstruction<'a> {
    fn to_string(&self) -> String {
        format!(
            "BranchNotEqual test: {} value: {}, jump: {}",
            self.test.to_string(),
            self.value.to_string(),
            self.jump.to_string()
        )
    }
}

impl<'a> Instruction for BranchNotEqualInstruction<'a> {
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

    fn jump_location(&self) -> Option<usize> {
        Some(self.jump)
    }
}

#[derive(Debug, Clone)]
struct AddInstruction<'a> {
    operand1: &'a Operand,
    operand2: &'a Operand,
    result: &'a Operand,
}

impl<'a> ToString for AddInstruction<'a> {
    fn to_string(&self) -> String {
        format!(
            "Add result: {}, operand1: {}, operand2 {}",
            self.result.to_string(),
            self.operand1.to_string(),
            self.operand2.to_string()
        )
    }
}

impl<'a> Instruction for AddInstruction<'a> {
    fn interpret(&self, machine: &mut Interpreter) -> Result<usize, Terminate> {
        let sum = machine.value(&self.operand1) + machine.value(&self.operand2);
        machine.store(&self.result, sum)?;
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
    source: &'a Operand,
}

impl<'a> ToString for PushInstruction<'a> {
    fn to_string(&self) -> String {
        format!("Push source: {}", self.source.to_string())
    }
}

impl<'a> Instruction for PushInstruction<'a> {
    fn interpret(&self, mut machine: &mut Interpreter) -> Result<usize, Terminate> {
        let value = machine.value(self.source);
        machine.stack.push(value);
        machine.sp += 1;
        Ok(machine.ipc + 1)
    }

    fn compile(&self, _machine: &mut Compiler) -> Result<usize, Terminate> {
        Err(Terminate::Unimplemented)
    }
}

#[derive(Debug, Clone)]
struct PopInstruction<'a> {
    result: &'a Operand,
}

impl<'a> ToString for PopInstruction<'a> {
    fn to_string(&self) -> String {
        format!("Pop result: {}", self.result.to_string())
    }
}

impl<'a> Instruction for PopInstruction<'a> {
    fn interpret(&self, mut machine: &mut Interpreter) -> Result<usize, Terminate> {
        let value = machine.stack.pop().unwrap();
        machine.store(&self.result, value)?;
        machine.sp -= 1;
        Ok(machine.ipc + 1)
    }

    fn compile(&self, _machine: &mut Compiler) -> Result<usize, Terminate> {
        Err(Terminate::Unimplemented)
    }
}

#[derive(Debug, Clone)]
struct StoreInstruction<'a> {
    result: &'a Operand,
    value: &'a Operand,
}

impl<'a> ToString for StoreInstruction<'a> {
    fn to_string(&self) -> String {
        format!(
            "Store result: {}, value: {}",
            self.result.to_string(),
            self.value.to_string(),
        )
    }
}

impl<'a> Instruction for StoreInstruction<'a> {
    fn interpret(&self, machine: &mut Interpreter) -> Result<usize, Terminate> {
        let value = machine.value(self.value);
        machine.store(&self.result, value)?;
        Ok(machine.ipc + 1)
    }

    fn compile(&self, _compiler: &mut Compiler) -> Result<usize, Terminate> {
        Err(Terminate::Unimplemented)
    }
}
