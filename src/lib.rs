extern crate log;
extern crate simple_logger;
use std::fmt::Debug;

mod compiler;
mod instruction;
mod interpreter;
mod operand;

// I tried making module fns for this but making the operand in that fn ended up
// making these lets in the tests would have lost the struct by the time it was
// used (e.g. let a = &operand::direct(1) -> Operand { tag: Direct, value: 1 }
macro_rules! direct {
    ($value:expr) => {{
        &Operand {
            tag: Tag::Direct,
            value: $value,
        }
    }};
}

macro_rules! literal {
    ($value:expr) => {{
        &Operand {
            tag: Tag::Literal,
            value: $value,
        }
    }};
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler::Compiler;
    use crate::instruction::instruction_set::*;
    use crate::instruction::Instruction;
    use crate::interpreter::Interpreter;
    use crate::operand::{Operand, Tag};

    #[test]
    fn test_interpreter_halt() {
        let program: &Vec<Box<dyn Instruction>> = &vec![halt()];
        Interpreter::new(program).execute().unwrap();
    }

    #[test]
    fn test_compiler_halt() {
        let program: &Vec<Box<dyn Instruction>> = &vec![halt()];
        assert!(Compiler::new(program).execute().unwrap().status.success());
    }

    #[test]
    fn test_interpreter_ran_off_end() {
        let a = direct!(0);
        let program: &Vec<Box<dyn Instruction>> = &vec![increment(a)];
        let result = Interpreter::new(program).execute();

        assert_eq!(result.err(), Some(Terminate::RanOffEnd))
    }

    #[test]
    fn test_interpreter_invalid_store() {
        let program: &Vec<Box<dyn Instruction>> = &vec![halt()];
        let mut interpreter = Interpreter::new(program);
        let value = literal!(0);
        let result = interpreter.store(&value, 0);

        assert_eq!(result.err(), Some(Terminate::RegisterInvalid));
    }

    #[test]
    fn test_interpreter_store_invalid_result() {
        let b = literal!(0);
        let program: &Vec<Box<dyn Instruction>> = &vec![store(b, b), halt()];
        let result = Interpreter::new(program).execute();

        assert_eq!(result.err(), Some(Terminate::RegisterInvalid));
    }

    #[test]
    fn test_interpreter_increment() {
        let b = direct!(0);
        let program: &Vec<Box<dyn Instruction>> = &vec![increment(b), increment(b), halt()];
        let mut interpreter = Interpreter::new(program);

        interpreter.step().unwrap();
        assert_eq!(interpreter.value(b), 1);

        interpreter.step().unwrap();
        assert_eq!(interpreter.value(b), 2);

        assert_eq!(interpreter.execute().unwrap(), ());
    }

    #[test]
    fn test_interpreter_increment_invalid_result() {
        let b = literal!(0);
        let program: &Vec<Box<dyn Instruction>> = &vec![increment(b), increment(b), halt()];
        let result = Interpreter::new(program).execute();

        assert_eq!(result.err(), Some(Terminate::RegisterInvalid));
    }

    #[test]
    fn test_compiler_increment() {
        let b = direct!(1);
        let program: &Vec<Box<dyn Instruction>> = &vec![increment(b), increment(b), halt()];
        let mut compiler = Compiler::new(program);

        assert_eq!(compiler.execute().unwrap().status.code().unwrap(), 2);
    }

    #[test]
    fn test_interpreter_add() {
        let a = direct!(0);
        let five = literal!(5);
        let one = literal!(1);
        let program: &Vec<Box<dyn Instruction>> = &vec![add(a, five, one), halt()];
        let mut interpreter = Interpreter::new(program);

        interpreter.execute().unwrap();

        assert_eq!(interpreter.value(a), 6);
    }

    #[test]
    fn test_compiler_add() {
        let b = direct!(1);
        let five = literal!(5);
        let one = literal!(1);
        let program: &Vec<Box<dyn Instruction>> = &vec![add(b, five, one), halt()];
        let mut compiler = Compiler::new(program);

        assert_eq!(compiler.execute().unwrap().status.code().unwrap(), 6);
    }

    #[test]
    fn test_interpreter_add_invalid_result() {
        let b = literal!(0);
        let program: &Vec<Box<dyn Instruction>> = &vec![add(b, b, b), halt()];
        let result = Interpreter::new(program).execute();

        assert_eq!(result.err(), Some(Terminate::RegisterInvalid));
    }

    #[test]
    fn test_compiler_add_no_mov() {
        let b = direct!(1);
        let five = literal!(5);
        let program: &Vec<Box<dyn Instruction>> = &vec![add(b, b, five), halt()];
        let mut compiler = Compiler::new(program);

        assert_eq!(compiler.execute().unwrap().status.code().unwrap(), 5);
    }

    #[test]
    fn test_interpreter_branch_not_equal() {
        let a = direct!(0);
        let b = direct!(1);
        let five = literal!(5);
        let program: &Vec<Box<dyn Instruction>> = &vec![
            store(a, five),
            increment(b),
            branch_not_equal(a, b, 1),
            halt(),
        ];
        Interpreter::new(program).execute().unwrap();
    }

    #[test]
    fn test_compiler_branch_not_equal() {
        let a = direct!(0);
        let b = direct!(1);
        // Jump past second increment so halt reports 1 instead of 2.
        let program: &Vec<Box<dyn Instruction>> = &vec![
            increment(b),
            branch_not_equal(a, b, 3),
            increment(b),
            halt(),
        ];
        let mut compiler = Compiler::new(program);

        assert_eq!(compiler.execute().unwrap().status.code().unwrap(), 1);
    }

    #[test]
    fn test_interpreter_push_pop() {
        let a = direct!(0);
        let b = direct!(1);
        let program: &Vec<Box<dyn Instruction>> = &vec![
            increment(a),
            push(a), // S: 1.
            increment(a),
            push(a), // S: 2, 1.
            pop(b),  // S: 1.
            halt(),
        ];
        let mut interpreter = Interpreter::new(program);

        assert_eq!(interpreter.stack_size(), 0);
        assert_eq!(interpreter.stack_peek(0), Err(Terminate::StackEmpty));

        interpreter.step_n(4).unwrap();

        assert_eq!(interpreter.stack_size(), 2);
        assert_eq!(interpreter.stack_peek(0).unwrap(), 2);
        assert_eq!(interpreter.stack_peek(1).unwrap(), 1);

        interpreter.step().unwrap();

        assert_eq!(interpreter.stack_size(), 1);
        assert_eq!(interpreter.stack_peek(0).unwrap(), 1);
        assert_eq!(interpreter.register_read(1).unwrap(), 2);

        interpreter.execute().unwrap();
    }

    #[test]
    fn test_interpreter_pop_invalid_result() {
        let b = literal!(0);
        let program: &Vec<Box<dyn Instruction>> = &vec![push(b), pop(b), halt()];
        let result = Interpreter::new(program).execute();

        assert_eq!(result.err(), Some(Terminate::RegisterInvalid));
    }
}

const REGISTERS_SIZE: usize = 32;
const STACK_SIZE: usize = 1024 * 1024;

type Registers = [i32; REGISTERS_SIZE];

#[derive(Debug, PartialEq)]
pub enum Terminate {
    RanOffEnd,
    ProgramHalted,
    Unimplemented,
    StackEmpty,
    RegisterInvalid,
}
