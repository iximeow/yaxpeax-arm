extern crate yaxpeax_arch;

use yaxpeax_arch::{Arch, Decodable, LengthedInstruction};

#[derive(Debug)]
pub enum Opcode {
    NOP
}

#[derive(Debug)]
pub struct Instruction {
    pub opcode: Opcode
}

impl LengthedInstruction for Instruction {
    type Unit = <PIC24 as Arch>::Address;
    fn len(&self) -> Self::Unit {
        3 // ish
    }
}

impl Decodable for Instruction {
    fn decode<'a, T: IntoIterator<Item=&'a u8>>(bytes: T) -> Option<Self> {
        let mut blank = Instruction { opcode: Opcode::NOP };
        match blank.decode_into(bytes) {
            Some(_) => Some(blank),
            None => None
        }
    }
    fn decode_into<'a, T: IntoIterator<Item=&'a u8>>(&mut self, bytes: T) -> Option<()> {
        match bytes.into_iter().next() {
            Some(0x00) => {
                self.opcode = Opcode::NOP;
                Some(())
            },
            _ => None
        }
    }
}

pub struct PIC24;
impl Arch for PIC24 {
    type Address = u32;
    type Instruction = Instruction;
    type Operand = ();
}
