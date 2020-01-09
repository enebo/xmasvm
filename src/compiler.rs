extern crate log;
extern crate simple_logger;
use crate::instruction::Instruction;
use crate::operand::{Operand, Tag};
use crate::Terminate;
use log::debug;
use std::fs;
use std::process::{Command, Output};

#[derive(Debug, Clone)]
pub struct Compiler<'a> {
    /// List of instructions we are going to translate
    program: &'a [Box<dyn Instruction>],
    /// The nasm program we will generate
    pub output: String,
}

/// Compiler targetting x86(32) nasm.
///
/// The instruction set was pretty arbitrarily chosen and intentionally not exactly
/// x86.  As such there needs to be some mappings.  For example, register 0 will end
/// up mapping to eax.  If for some reason an x86 instr ends up putting something into
/// eax then it may wipe out our original user of register 0.
impl Compiler<'_> {
    pub(crate) fn new<'a>(program: &'a [Box<dyn Instruction>]) -> Compiler {
        Compiler {
            program,
            /// Input to be written out for 'nasm' to assemble.
            output: String::new(),
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

    /// Try and execute the nasm file we compiled to an executable.
    fn call_executable(&self) -> Output {
        Command::new("./xmasvm")
            .output()
            .expect("Could not find xmasvm")
    }

    /// Compile our program to nasm.
    pub(crate) fn execute(&mut self) -> Result<Output, Terminate> {
        // FIXME: init can only be called once to init so just ignore errors.  Ultimately, this should be passed in.
        match simple_logger::init() {
            _ => {}
        }

        let labels = self.calculate_labels();

        self.write_prologue();

        for (ipc, label) in labels.iter().enumerate() {
            debug!("EMITTING IPC {}", ipc);

            let instruction = &*self.program[ipc];

            if *label != 0 {
                self.output.push_str("\n_");
                self.output.push_str(ipc.to_string().as_ref());
                self.output.push_str(":\n");
            }

            match instruction.compile(self) {
                Ok(_) => {}
                Err(err) => return Err(err),
            }
        }

        self.write_epilogue();

        debug!("NASM OUTPUT:\n{}", self.output);

        fs::write("xmasvm.asm", &self.output).expect("Could not write asm file?");

        self.generate_executable();
        Ok(self.call_executable())
    }

    /// Assemble and link our program.
    fn generate_executable(&self) {
        Command::new("nasm")
            .arg("-f")
            .arg("elf32")
            .arg("xmasvm.asm")
            .arg("-o")
            .arg("xmasvm.o")
            .output()
            .expect("Could not execute nasm");

        Command::new("ld")
            .arg("-m")
            .arg("elf_i386")
            .arg("xmasvm.o")
            .arg("-o")
            .arg("xmasvm")
            .output()
            .expect("Count not execute ld");
    }

    /// Given a virtual machine operand which x86 instr should we use?...or die tryin'
    pub(crate) fn native_register_for(&self, operand: &Operand) -> Result<String, Terminate> {
        if operand.tag == Tag::Literal {
            return Err(Terminate::RegisterInvalid);
        }

        match (operand.value, operand.tag) {
            (0, Tag::Direct) => Ok("eax".to_string()),
            (0, Tag::Indirect) => Ok("[eax]".to_string()),
            (1, Tag::Direct) => Ok("ebx".to_string()),
            (1, Tag::Indirect) => Ok("[ebx]".to_string()),
            _ => Err(Terminate::RegisterInvalid),
        }
    }

    /// Given a virtual machine operand which value or x86 register should we use.
    pub(crate) fn native_register_or_value(&self, operand: &Operand) -> Result<String, Terminate> {
        let register = self.native_register_for(operand);

        match register {
            Err(Terminate::RegisterInvalid) if operand.tag == Tag::Literal => {
                Ok(operand.value.to_string())
            }
            _ => register,
        }
    }

    fn write_prologue(&mut self) {
        self.output.push_str("global _start\n");
        self.output.push_str("section .text\n");
        self.output.push_str("_start:\n");
    }

    fn write_epilogue(&mut self) {
        self.output
            .push_str(";;;;; Pushed with xmasvm...ho ho ho\n");
    }
}
