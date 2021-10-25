//#[cfg(feature="use-serde")]
//use serde::{Serialize, Deserialize};

use core::fmt::{self, Display, Formatter};

use yaxpeax_arch::{Arch, AddressDiff, Decoder, LengthedInstruction, Reader, ReadError, ShowContextual, YaxColors};

#[allow(non_snake_case)]
mod docs {
    use crate::armv8::a64::DecodeError;

    #[test]
    fn test_ones() {
        assert_eq!(Ones(0), 0x00);
        assert_eq!(Ones(1), 0x01);
        assert_eq!(Ones(2), 0x03);
        assert_eq!(Ones(3), 0x07);
        assert_eq!(Ones(4), 0x0f);
        assert_eq!(Ones(5), 0x1f);
        assert_eq!(Ones(6), 0x3f);
        assert_eq!(Ones(7), 0x7f);
        assert_eq!(Ones(8), 0xff);
    }

    fn Ones(len: u8) -> u64 {
        assert!(len <= 64);

        if len == 0 { return 0; }
        if len == 64 { return 0xffffffff_ffffffffu64; }

        let mask = ((0x8000_0000_0000_0000u64 as i64) >> ((64 - 1) - len)) as u64;
        !mask
    }

    #[test]
    fn test_highest_set_bit() {
        assert_eq!(HighestSetBit(1, 0x11), 0);
        assert_eq!(HighestSetBit(5, 0x11), 4);
        assert_eq!(HighestSetBit(8, 0x08), 3);
    }

    fn HighestSetBit(N: u8, bits: u64) -> u8 {
        let mut probe = 1u64 << (N - 1);
        let mut i = N - 1;
        loop {
            if bits & probe != 0 {
                return i;
            }

            if i == 0 {
                break;
            } else {
                probe = probe >> 1;
                i -= 1;
            }
        }

        return 0xff;
    }

    fn Replicate(bitsM: u64, M_size: u8, N: u8) -> u64 {
        let count = N / M_size;
        let mut res = bitsM;
        for i in 1..count {
            res |= bitsM << M_size * i;
        }
        // since this produces a u64, we might have a few extra non-zero bits set.
        let res_mask = Ones(N);
        res & res_mask
    }

    fn ROR(bits: u64, bitsN: u8, shift: u8) -> u64 {
        if shift == 0 {
            bits
        } else {
            let m = shift % bitsN;
            (bits >> m) | (bits << (bitsN - m))
        }
    }

    // helper functions from the ARMv8 Architecture Reference Manual
    pub fn DecodeBitMasks_32(immN: u8, imms: u8, immr: u8) -> Result<(u32, u32), DecodeError> {
        // should the !imms be ~imms
        let len = HighestSetBit(7, ((immN << 6) | ((!imms) & 0x3f)) as u64);
        if len == 0xff {
            return Err(DecodeError::InvalidOperand);
        }

        let levels = (Ones(len) & 0x3f) as u8; // should ZeroExtend to at least 6 bits, but this is u8.

        let S = imms & levels;
        let R = immr & levels;
        let diff = S.wrapping_sub(R);

        let esize = 1 << len;
        let d = diff & !(0xff << len);
        let welem = Ones(S + 1);
        let telem = Ones(d + 1);
        let wmask = Replicate(ROR(welem, esize, R), esize, 32) as u32;
        let tmask = Replicate(telem, esize, 32) as u32;
        Ok((wmask, tmask))
    }

    pub fn DecodeBitMasks_64(immN: u8, imms: u8, immr: u8) -> Result<(u64, u64), DecodeError> {
        // should the !imms be ~imms
        let len = HighestSetBit(7, ((immN << 6) | ((!imms) & 0x3f)) as u64);
        if len == 0xff {
            return Err(DecodeError::InvalidOperand);
        }

        let levels = (Ones(len) & 0x3f) as u8; // should ZeroExtend to at least 6 bits, but this is u8.

        let S = imms & levels;
        let R = immr & levels;
        let diff = S.wrapping_sub(R);

        let esize = 1 << len;
        let d = diff & !(0xff << len);
        let welem = Ones(S + 1);
        let telem = Ones(d + 1);
        let wmask = Replicate(ROR(welem, esize, R), esize, 64);
        let tmask = Replicate(telem, esize, 64);
        Ok((wmask, tmask))
    }

    pub fn DecodeShift(op: u8) -> super::ShiftStyle {
        assert!(op <= 0b11);
        [
            super::ShiftStyle::LSL,
            super::ShiftStyle::LSR,
            super::ShiftStyle::ASR,
            super::ShiftStyle::ROR,
        ][op as usize]
    }
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum DecodeError {
    ExhaustedInput,
    InvalidOpcode,
    InvalidOperand,
    IncompleteDecoder,
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f:  &mut fmt::Formatter) -> fmt::Result {
        use yaxpeax_arch::DecodeError;
        f.write_str(self.description())
    }
}

#[cfg(feature = "std")]
extern crate std;
#[cfg(feature = "std")]
impl std::error::Error for DecodeError {
    fn description(&self) -> &str {
        <Self as yaxpeax_arch::DecodeError>::description(self)
    }
}

impl From<ReadError> for DecodeError {
    fn from(_e: ReadError) -> DecodeError {
        DecodeError::ExhaustedInput
    }
}

impl yaxpeax_arch::DecodeError for DecodeError {
    fn data_exhausted(&self) -> bool { self == &DecodeError::ExhaustedInput }
    fn bad_opcode(&self) -> bool { self == &DecodeError::InvalidOpcode }
    fn bad_operand(&self) -> bool { self == &DecodeError::InvalidOperand }
    fn description(&self) -> &'static str {
        match self {
            DecodeError::ExhaustedInput => "exhausted input",
            DecodeError::InvalidOpcode => "invalid opcode",
            DecodeError::InvalidOperand => "invalid operand",
            DecodeError::IncompleteDecoder => "incomplete decoder",
        }
    }
}

impl yaxpeax_arch::Instruction for Instruction {
    // TODO: this is wrong!!
    fn well_defined(&self) -> bool { true }
}

pub struct NoContext;

impl <T: fmt::Write, Y: YaxColors> ShowContextual<u64, NoContext, T, Y> for Instruction {
    fn contextualize(&self, _colors: &Y, _address: u64, _context: Option<&NoContext>, out: &mut T) -> fmt::Result {
        write!(out, "{}", self)
    }
}

#[cfg(feature="use-serde")]
#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub struct ARMv8 { }

#[cfg(not(feature="use-serde"))]
#[derive(Copy, Clone, Debug)]
pub struct ARMv8 { }

impl Arch for ARMv8 {
    type Word = u8;
    type Address = u64;
    type Instruction = Instruction;
    type DecodeError = DecodeError;
    type Decoder = InstDecoder;
    type Operand = Operand;
}

#[derive(Copy, Clone, Debug, PartialEq)]
#[repr(u8)]
pub enum SizeCode { X, W }

#[derive(Copy, Clone, Debug, PartialEq)]
#[repr(u8)]
pub enum SIMDSizeCode { S, D, Q }

#[derive(Copy, Clone, Debug, PartialEq)]
#[repr(C)]
pub struct Instruction {
    pub opcode: Opcode,
    pub operands: [Operand; 4],
}

impl Display for Instruction {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        match self.opcode {
            Opcode::Invalid => {
                write!(fmt, "invalid")?;
            },
            Opcode::MOVN => {
                let imm = if let Operand::ImmShift(imm, shift) = self.operands[1] {
                    !((imm as u64) << shift)
                } else {
                    unreachable!("movn operand 1 is always ImmShift");
                };
                let imm = if let Operand::Register(size, _) = self.operands[0] {
                    if size == SizeCode::W {
                        (imm as u32) as u64
                    } else {
                        imm
                    }
                } else {
                    unreachable!("movn operand 0 is always Register");
                };
                return write!(fmt, "mov {}, {:#x}", self.operands[0], imm);
            },
            Opcode::MOVK => {
                write!(fmt, "movk")?;
            },
            Opcode::MOVZ => {
                let imm = if let Operand::ImmShift(imm, shift) = self.operands[1] {
                    (imm as u64) << shift
                } else {
                    unreachable!("movz operand is always ImmShift");
                };
                let imm = if let Operand::Register(size, _) = self.operands[0] {
                    if size == SizeCode::W {
                        (imm as u32) as u64
                    } else {
                        imm
                    }
                } else {
                    unreachable!("movn operand 0 is always Register");
                };
                return write!(fmt, "mov {}, {:#x}", self.operands[0], imm);
            },
            Opcode::ADC => {
                write!(fmt, "adc")?;
            },
            Opcode::ADCS => {
                write!(fmt, "adcs")?;
            },
            Opcode::SBC => {
                write!(fmt, "sbc")?;
            },
            Opcode::SBCS => {
                write!(fmt, "sbcs")?;
            },
            Opcode::AND => {
                write!(fmt, "and")?;
            },
            Opcode::BIC => {
                write!(fmt, "bic")?;
            },
            Opcode::BICS => {
                write!(fmt, "bics")?;
            },
            Opcode::ORR => {
                if let Operand::Register(_, 31) = self.operands[1] {
                    if let Operand::Immediate(0) = self.operands[2] {
                        return write!(fmt, "mov {}, {}", self.operands[0], self.operands[1]);
                    } else if let Operand::RegShift(ShiftStyle::LSL, 0, size, r) = self.operands[2] {
                        return write!(fmt, "mov {}, {}", self.operands[0], Operand::Register(size, r));
                    } else {
                        return write!(fmt, "mov {}, {}", self.operands[0], self.operands[2]);
                    }
                }
                write!(fmt, "orr")?;
            },
            Opcode::ORN => {
                if let Operand::Register(_, 31) = self.operands[1] {
                    return write!(fmt, "mvn {}, {}", self.operands[0], self.operands[2]);
                }
                write!(fmt, "orn")?;
            },
            Opcode::EOR => {
                write!(fmt, "eor")?;
            },
            Opcode::EON => {
                write!(fmt, "eon")?;
            },
            Opcode::ANDS => {
                if let Operand::Register(_, 31) = self.operands[0] {
                    return write!(fmt, "tst {}, {}", self.operands[1], self.operands[2]);
                }
                write!(fmt, "ands")?;
            },
            Opcode::ADDS => {
                if let Operand::Register(_, 31) = self.operands[0] {
                    return write!(fmt, "cmn {}, {}", self.operands[1], self.operands[2]);
                } else if let Operand::RegShift(ShiftStyle::LSL, 0, size, reg) = self.operands[2] {
                    return write!(fmt, "adds {}, {}, {}", self.operands[0], self.operands[1], Operand::RegisterOrSP(size, reg));
                }
                write!(fmt, "adds")?;
            },
            Opcode::ADD => {
                if let Operand::Immediate(0) = self.operands[2] {
                    if let Operand::Register(_, 31) = self.operands[0] {
                        return write!(fmt, "mov {}, {}", self.operands[0], self.operands[1]);
                    } else if let Operand::RegisterOrSP(_, 31) = self.operands[1] {
                        return write!(fmt, "mov {}, {}", self.operands[0], self.operands[1]);
                    }
                } else if let Operand::RegShift(ShiftStyle::LSL, 0, size, reg) = self.operands[2] {
                    return write!(fmt, "add {}, {}, {}", self.operands[0], self.operands[1], Operand::RegisterOrSP(size, reg));
                }
                write!(fmt, "add")?;
            },
            Opcode::SUBS => {
                if let Operand::Register(_, 31) = self.operands[0] {
                    crate::armv8::a64::std::eprintln!("{:?}", self);
                    return write!(fmt, "cmp {}, {}", self.operands[1], self.operands[2])
                } else if let Operand::Register(_, 31) = self.operands[1] {
                    return write!(fmt, "negs {}, {}", self.operands[0], self.operands[2])
                } else if let Operand::RegShift(ShiftStyle::LSL, 0, size, reg) = self.operands[2] {
                    return write!(fmt, "subs {}, {}, {}", self.operands[0], self.operands[1], Operand::RegisterOrSP(size, reg));
                }
                write!(fmt, "subs")?;
            },
            Opcode::SUB => {
                if let Operand::Register(_, 31) = self.operands[1] {
                    return write!(fmt, "neg {}, {}", self.operands[0], self.operands[2])
                } else if let Operand::RegShift(ShiftStyle::LSL, 0, size, reg) = self.operands[2] {
                    return write!(fmt, "sub {}, {}, {}", self.operands[0], self.operands[1], Operand::RegisterOrSP(size, reg));
                }
                write!(fmt, "sub")?;
            },
            Opcode::BFM => {
                write!(fmt, "bfm")?;
            },
            Opcode::UBFM => {
                if let Operand::Immediate(0) = self.operands[2] {
                    let newdest = if let Operand::Register(_size, destnum) = self.operands[0] {
                        Operand::Register(SizeCode::W, destnum)
                    } else {
                        unreachable!("operand 1 is always a register");
                    };
                    let newsrc = if let Operand::Register(_size, srcnum) = self.operands[1] {
                        Operand::Register(SizeCode::W, srcnum)
                    } else {
                        unreachable!("operand 1 is always a register");
                    };
                    if let Operand::Immediate(7) = self.operands[3] {
                        return write!(fmt, "uxtb {}, {}", newdest, newsrc);
                    } else if let Operand::Immediate(15) = self.operands[3] {
                        return write!(fmt, "uxth {}, {}", newdest, newsrc);
                    }
                }
                if let Operand::Immediate(imms) = self.operands[3] {
                    let size = if let Operand::Register(size, _) = self.operands[0] {
                        size
                    } else {
                        unreachable!("operand 0 is a register");
                    };
                    match (imms, size) {
                        (63, SizeCode::X) |
                        (31, SizeCode::W) => {
                            return write!(fmt, "lsr {}, {}, {}", self.operands[0], self.operands[1], self.operands[2]);
                        },
                        _ => {
                            let size = if size == SizeCode::X {
                                64
                            } else {
                                32
                            };
                            let immr = if let Operand::Immediate(immr) = self.operands[2] {
                                immr
                            } else {
                                unreachable!("operand 3 is a register");
                            };
                            if imms + 1 == immr {
                                return write!(fmt, "lsl {}, {}, {:#x}", self.operands[0], self.operands[1], size - imms - 1);
                            }
                            if imms < immr {
                                return write!(fmt, "ubfiz {}, {}, {:#x}, {:#x}",
                                    self.operands[0],
                                    self.operands[1],
                                    size - immr,
                                    imms + 1,
                                );
                            }
                        }
                    }
                }
                write!(fmt, "ubfm")?;
            },
            Opcode::SBFM => {
                if let Operand::Immediate(0) = self.operands[2] {
                    let newsrc = if let Operand::Register(_size, srcnum) = self.operands[1] {
                        Operand::Register(SizeCode::W, srcnum)
                    } else {
                        unreachable!("operand 1 is always a register");
                    };
                    if let Operand::Immediate(7) = self.operands[3] {
                        return write!(fmt, "sxtb {}, {}", self.operands[0], newsrc);
                    } else if let Operand::Immediate(15) = self.operands[3] {
                        return write!(fmt, "sxth {}, {}", self.operands[0], newsrc);
                    } else if let Operand::Immediate(31) = self.operands[3] {
                        return write!(fmt, "sxtw {}, {}", self.operands[0], newsrc);
                    }
                }
                if let Operand::Immediate(63) = self.operands[3] {
                    if let Operand::Register(SizeCode::X, _) = self.operands[0] {
                        return write!(fmt, "asr {}, {}, {}", self.operands[0], self.operands[1], self.operands[2]);
                    }
                }
                if let Operand::Immediate(31) = self.operands[3] {
                    if let Operand::Register(SizeCode::W, _) = self.operands[0] {
                        return write!(fmt, "asr {}, {}, {}", self.operands[0], self.operands[1], self.operands[2]);
                    }
                }
                if let (Operand::Immediate(imms), Operand::Immediate(immr)) = (self.operands[2], self.operands[3]) {
                    if immr < imms {
                        let size = if let Operand::Register(size, _) = self.operands[0] {
                            if size == SizeCode::W {
                                32
                            } else {
                                64
                            }
                        } else {
                            unreachable!("operand 0 is always a register");
                        };
                        return write!(fmt, "sbfiz {}, {}, {:#x}, {:#x}",
                            self.operands[0],
                            self.operands[1],
                            size - imms,
                            immr + 1,
                        );
                    }
                }
                write!(fmt, "sbfm")?;
            },
            Opcode::ADR => {
                write!(fmt, "adr")?;
            },
            Opcode::ADRP => {
                write!(fmt, "adrp")?;
            },
            Opcode::EXTR => {
                write!(fmt, "extr")?;
            },
            Opcode::LDP => {
                write!(fmt, "ldp")?;
            },
            Opcode::LDPSW => {
                write!(fmt, "ldpsw")?;
            },
            Opcode::LDR => {
                write!(fmt, "ldr")?;
            },
            Opcode::LDRB => {
                write!(fmt, "ldrb")?;
            },
            Opcode::LDRSB => {
                write!(fmt, "ldrsb")?;
            },
            Opcode::LDRSH => {
                write!(fmt, "ldrsh")?;
            },
            Opcode::LDRSW => {
                write!(fmt, "ldrsw")?;
            },
            Opcode::LDRH => {
                write!(fmt, "ldrh")?;
            },
            Opcode::LDTR => {
                write!(fmt, "ldtr")?;
            },
            Opcode::LDTRB => {
                write!(fmt, "ldtrb")?;
            },
            Opcode::LDTRSB => {
                write!(fmt, "ldtrsb")?;
            },
            Opcode::LDTRSH => {
                write!(fmt, "ldtrsh")?;
            },
            Opcode::LDTRSW => {
                write!(fmt, "ldtrsw")?;
            },
            Opcode::LDTRH => {
                write!(fmt, "ldtrh")?;
            },
            Opcode::LDUR => {
                write!(fmt, "ldur")?;
            },
            Opcode::LDURB => {
                write!(fmt, "ldurb")?;
            },
            Opcode::LDURSB => {
                write!(fmt, "ldursb")?;
            },
            Opcode::LDURSW => {
                write!(fmt, "ldursw")?;
            },
            Opcode::LDURSH => {
                write!(fmt, "ldursh")?;
            },
            Opcode::LDURH => {
                write!(fmt, "ldurh")?;
            },
            Opcode::LDAR => {
                write!(fmt, "ldar")?;
            },
            Opcode::LDARB => {
                write!(fmt, "ldarb")?;
            },
            Opcode::LDAXRB => {
                write!(fmt, "ldaxrb")?;
            },
            Opcode::LDARH => {
                write!(fmt, "ldarh")?;
            },
            Opcode::LDAXP => {
                write!(fmt, "ldaxp")?;
            },
            Opcode::LDAXR => {
                write!(fmt, "ldaxr")?;
            },
            Opcode::LDAXRH => {
                write!(fmt, "ldaxrh")?;
            },
            Opcode::LDXP => {
                write!(fmt, "ldxp")?;
            },
            Opcode::LDXR => {
                write!(fmt, "ldxr")?;
            },
            Opcode::LDXRB => {
                write!(fmt, "ldxrb")?;
            },
            Opcode::LDXRH => {
                write!(fmt, "ldxrh")?;
            },
            Opcode::STP => {
                write!(fmt, "stp")?;
            },
            Opcode::STR => {
                write!(fmt, "str")?;
            },
            Opcode::STRB => {
                write!(fmt, "strb")?;
            },
            Opcode::STRH => {
                write!(fmt, "strh")?;
            },
            Opcode::STRW => {
                write!(fmt, "strw")?;
            },
            Opcode::STTR => {
                write!(fmt, "sttr")?;
            },
            Opcode::STTRB => {
                write!(fmt, "sttrb")?;
            },
            Opcode::STTRH => {
                write!(fmt, "sttrh")?;
            },
            Opcode::STUR => {
                write!(fmt, "stur")?;
            },
            Opcode::STURB => {
                write!(fmt, "sturb")?;
            },
            Opcode::STURH => {
                write!(fmt, "sturh")?;
            },
            Opcode::STLR => {
                write!(fmt, "stlr")?;
            },
            Opcode::STLRB => {
                write!(fmt, "stlrb")?;
            },
            Opcode::STLRH => {
                write!(fmt, "stlrh")?;
            },
            Opcode::STLXP => {
                write!(fmt, "stlxp")?;
            },
            Opcode::STLXR => {
                write!(fmt, "stlxr")?;
            },
            Opcode::STLXRB => {
                write!(fmt, "stlxrb")?;
            },
            Opcode::STLXRH => {
                write!(fmt, "stlxrh")?;
            },
            Opcode::STXP => {
                write!(fmt, "stxp")?;
            },
            Opcode::STXR => {
                write!(fmt, "stxr")?;
            },
            Opcode::STXRB => {
                write!(fmt, "stxrb")?;
            },
            Opcode::STXRH => {
                write!(fmt, "stxrh")?;
            },
            Opcode::TBZ => {
                write!(fmt, "tbz")?;
            },
            Opcode::TBNZ => {
                write!(fmt, "tbnz")?;
            },
            Opcode::CBZ => {
                write!(fmt, "cbz")?;
            },
            Opcode::CBNZ => {
                write!(fmt, "cbnz")?;
            },
            Opcode::B => {
                write!(fmt, "b")?;
            },
            Opcode::BR => {
                write!(fmt, "br")?;
            },
            Opcode::Bcc(cond) => {
                write!(fmt, "b.{}", Operand::ConditionCode(cond))?;
            },
            Opcode::BL => {
                write!(fmt, "bl")?;
            },
            Opcode::BLR => {
                write!(fmt, "blr")?;
            },
            Opcode::SVC => {
                write!(fmt, "svc")?;
            },
            Opcode::HVC => {
                write!(fmt, "hvc")?;
            },
            Opcode::SMC => {
                write!(fmt, "smc")?;
            },
            Opcode::BRK => {
                write!(fmt, "brk")?;
            },
            Opcode::HLT => {
                write!(fmt, "hlt")?;
            },
            Opcode::DCPS1 => {
                write!(fmt, "dcps1")?;
            },
            Opcode::DCPS2 => {
                write!(fmt, "dcps2")?;
            },
            Opcode::DCPS3 => {
                write!(fmt, "dcps3")?;
            },
            Opcode::RET => {
                write!(fmt, "ret")?;
                if let Operand::Register(SizeCode::X, 30) = self.operands[0] {
                    // C5.6.148:  Defaults to X30 if absent.
                    // so ret x30 is probably expected to be read as just `ret`
                    return Ok(());
                }
            },
            Opcode::ERET => {
                write!(fmt, "eret")?;
            },
            Opcode::DRPS => {
                write!(fmt, "drps")?;
            },
            Opcode::MSRa(a, b) => {
                write!(fmt, "msr(a) {}, {}", a, b)?;
            }
            Opcode::MSRb(a) => {
                write!(fmt, "msr(b) {:#x}", a)?;
            }
            Opcode::MRS(v) => {
                write!(fmt, "mrs({:#x})", v)?;
            }
            Opcode::SYS => {
                write!(fmt, "sys")?;
            }
            Opcode::SYSL => {
                write!(fmt, "sys")?;
            }
            Opcode::ISB => {
                write!(fmt, "isb")?;
            }
            Opcode::DSB => {
                write!(fmt, "dsb")?;
            }
            Opcode::DMB => {
                write!(fmt, "dmb")?;
            }
            Opcode::HINT(v) => {
                match v {
                    0 => { write!(fmt, "nop")?; },
                    1 => { write!(fmt, "yield")?; },
                    2 => { write!(fmt, "wfe")?; },
                    3 => { write!(fmt, "wfi")?; },
                    4 => { write!(fmt, "sev")?; },
                    5 => { write!(fmt, "sevl")?; },
                    _ => { write!(fmt, "hint({:#x})", v)?; }
                }
            }
            Opcode::CLREX => {
                write!(fmt, "clrex")?;
            }
            Opcode::CSEL => {
                write!(fmt, "csel")?;
            }
            Opcode::CSNEG => {
                write!(fmt, "csneg")?;
            }
            Opcode::CSINC => {
                match (self.operands[1], self.operands[2], self.operands[3]) {
                    (Operand::Register(_, n), Operand::Register(_, m), Operand::ConditionCode(cond)) => {
                        if n == m && cond < 0b1110 {
                            if n == 31 {
                                return write!(fmt, "cset {}, {}", self.operands[0], Operand::ConditionCode(cond ^ 0x01));
                            } else {
                                return write!(fmt, "cinc {}, {}, {}", self.operands[0], self.operands[1], Operand::ConditionCode(cond ^ 0x01));
                            }
                        }
                    }
                    _ => {}
                }
                write!(fmt, "csinc")?;
            }
            Opcode::CSINV => {
                match (self.operands[1], self.operands[2], self.operands[3]) {
                    (Operand::Register(_, n), Operand::Register(_, m), Operand::ConditionCode(cond)) => {
                        if n == m && n != 31 && cond < 0b1110 {
                            return write!(fmt, "cinv {}, {}, {}", self.operands[0], self.operands[1], Operand::ConditionCode(cond ^ 0x01))
                        }
                    }
                    _ => {}
                }
                write!(fmt, "csinv")?;
            }
            Opcode::PACIA => {
                write!(fmt, "pacia")?;
            }
            Opcode::PACIZA => {
                write!(fmt, "paciza")?;
            }
            Opcode::CCMN => {
                write!(fmt, "ccmn")?;
            }
            Opcode::CCMP => {
                write!(fmt, "ccmp")?;
            }
            Opcode::RBIT => {
                write!(fmt, "rbit")?;
            }
            Opcode::REV16 => {
                write!(fmt, "rev16")?;
            }
            Opcode::REV => {
                write!(fmt, "rev")?;
            }
            Opcode::REV32 => {
                write!(fmt, "rev32")?;
            }
            Opcode::CLZ => {
                write!(fmt, "clz")?;
            }
            Opcode::CLS => {
                write!(fmt, "cls")?;
            }
            Opcode::MADD => {
                write!(fmt, "madd")?;
            }
            Opcode::MSUB => {
                write!(fmt, "msub")?;
            }
            Opcode::SMADDL => {
                write!(fmt, "smaddl")?;
            }
            Opcode::SMSUBL => {
                write!(fmt, "smsubl")?;
            }
            Opcode::SMULH => {
                write!(fmt, "smulh")?;
            }
            Opcode::UMADDL => {
                write!(fmt, "umaddl")?;
            }
            Opcode::UMSUBL => {
                write!(fmt, "umsubl")?;
            }
            Opcode::UMULH => {
                write!(fmt, "umulh")?;
            }
        };

        if self.operands[0] != Operand::Nothing {
            write!(fmt, " {}", self.operands[0])?;
        } else {
            return Ok(());
        }

        if self.operands[1] != Operand::Nothing {
            write!(fmt, ", {}", self.operands[1])?;
        } else {
            return Ok(());
        }

        if self.operands[2] != Operand::Nothing {
            write!(fmt, ", {}", self.operands[2])?;
        } else {
            return Ok(());
        }

        if self.operands[3] != Operand::Nothing {
            write!(fmt, ", {}", self.operands[3])?;
        } else {
            return Ok(());
        }

        Ok(())
    }
}

impl LengthedInstruction for Instruction {
    type Unit = AddressDiff<<ARMv8 as Arch>::Address>;
    fn min_size() -> Self::Unit {
        AddressDiff::from_const(4)
    }
    fn len(&self) -> Self::Unit {
        AddressDiff::from_const(4)
    }
}

impl Default for Instruction {
    fn default() -> Self {
        Instruction {
            opcode: Opcode::Invalid,
            operands: [Operand::Nothing, Operand::Nothing, Operand::Nothing, Operand::Nothing]
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
#[repr(u8)]
pub enum Opcode {
    Invalid,
    MOVN,
    MOVK,
    MOVZ,
    ADC,
    ADCS,
    SBC,
    SBCS,
    AND,
    ORR,
    ORN,
    EOR,
    EON,
    BIC,
    BICS,
    ANDS,
    ADDS,
    ADD,
    SUBS,
    SUB,
    BFM,
    UBFM,
    SBFM,
    ADR,
    ADRP,
    EXTR,
    LDAR,
    LDARB,
    LDAXRB,
    LDARH,
    LDAXP,
    LDAXR,
    LDAXRH,
    LDP,
    LDPSW,
    LDR,
    LDRB,
    LDRSB,
    LDRSW,
    LDRSH,
    LDRH,
    LDTR,
    LDTRB,
    LDTRH,
    LDTRSB,
    LDTRSH,
    LDTRSW,
    LDUR,
    LDURB,
    LDURSB,
    LDURSW,
    LDURSH,
    LDURH,
    LDXP,
    LDXR,
    LDXRB,
    LDXRH,
    STLR,
    STLRB,
    STLRH,
    STLXP,
    STLXR,
    STLXRB,
    STLXRH,
    STP,
    STR,
    STTR,
    STTRB,
    STTRH,
    STRB,
    STRH,
    STRW,
    STUR,
    STURB,
    STURH,
    STXP,
    STXR,
    STXRB,
    STXRH,
    TBZ,
    TBNZ,
    CBZ,
    CBNZ,
    B,
    BR,
    Bcc(u8),
    BL,
    BLR,
    SVC,
    HVC,
    SMC,
    BRK,
    HLT,
    DCPS1,
    DCPS2,
    DCPS3,
    RET,
    ERET,
    DRPS,
    MSRa(u8, u8),
    MSRb(u32),
    MRS(u32),
    SYS,
    SYSL,
    ISB,
    DSB,
    DMB,
    HINT(u8),
    CLREX,
    CSEL,
    CSNEG,
    CSINC,
    CSINV,
    PACIA,
    PACIZA,
    CCMN,
    CCMP,
    RBIT,
    REV16,
    REV,
    REV32,
    CLZ,
    CLS,
    MADD,
    MSUB,
    SMADDL,
    SMSUBL,
    SMULH,
    UMADDL,
    UMSUBL,
    UMULH,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum ShiftStyle {
    LSL,
    LSR,
    ASR,
    ROR,
    UXTB,
    UXTH,
    UXTW,
    UXTX,
    SXTB,
    SXTH,
    SXTW,
    SXTX,
}

impl Display for ShiftStyle {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ShiftStyle::LSL => { write!(fmt, "lsl") },
            ShiftStyle::LSR => { write!(fmt, "lsr") },
            ShiftStyle::ASR => { write!(fmt, "asr") },
            ShiftStyle::ROR => { write!(fmt, "ror") },
            ShiftStyle::UXTB => { write!(fmt, "uxtb") },
            ShiftStyle::UXTH => { write!(fmt, "uxth") },
            ShiftStyle::UXTW => { write!(fmt, "uxtw") },
            ShiftStyle::UXTX => { write!(fmt, "uxtx") },
            ShiftStyle::SXTB => { write!(fmt, "sxtb") },
            ShiftStyle::SXTH => { write!(fmt, "sxth") },
            ShiftStyle::SXTW => { write!(fmt, "sxtw") },
            ShiftStyle::SXTX => { write!(fmt, "sxtx") },
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
#[repr(C)]
pub enum Operand {
    Nothing,
    Register(SizeCode, u16),
    SIMDRegister(SIMDSizeCode, u16),
    RegisterOrSP(SizeCode, u16),
    ConditionCode(u8),
    Offset(i64),
    PCOffset(i64),
    Immediate(u32),
    Imm64(u64),
    Imm16(u16),
    ImmShift(u16, u8),
    RegShift(ShiftStyle, u8, SizeCode, u16),
    RegOffset(u16, i16),
    RegRegOffset(u16, SizeCode, u16, ShiftStyle, u8),
    RegPreIndex(u16, i16),
    RegPostIndex(u16, i16),
}

impl Display for Operand {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        match self {
            Operand::Nothing => {
                unreachable!();
            },
            Operand::Register(size, reg) => {
                if *reg == 31 {
                    match size {
                        SizeCode::X => {
                            write!(fmt, "xzr")
                        },
                        SizeCode::W => {
                            write!(fmt, "wzr")
                        }
                    }
                } else {
                    match size {
                        SizeCode::X => {
                            write!(fmt, "x{}", reg)
                        },
                        SizeCode::W => {
                            write!(fmt, "w{}", reg)
                        }
                    }
                }
            },
            Operand::SIMDRegister(size, reg) => {
                match size {
                    SIMDSizeCode::S => { write!(fmt, "s{}", reg) }
                    SIMDSizeCode::D => { write!(fmt, "d{}", reg) }
                    SIMDSizeCode::Q => { write!(fmt, "q{}", reg) }
                }
            }
            Operand::RegisterOrSP(size, reg) => {
                if *reg == 31 {
                    match size {
                        SizeCode::X => {
                            write!(fmt, "sp")
                        },
                        SizeCode::W => {
                            write!(fmt, "wsp")
                        }
                    }
                } else {
                    match size {
                        SizeCode::X => {
                            write!(fmt, "x{}", reg)
                        },
                        SizeCode::W => {
                            write!(fmt, "w{}", reg)
                        }
                    }
                }
            },
            Operand::ConditionCode(cond) => {
                match cond {
                    0b0000 => { write!(fmt, "eq") }
                    0b0010 => { write!(fmt, "hs") }
                    0b0100 => { write!(fmt, "mi") }
                    0b0110 => { write!(fmt, "vs") }
                    0b1000 => { write!(fmt, "hi") }
                    0b1010 => { write!(fmt, "ge") }
                    0b1100 => { write!(fmt, "gt") }
                    0b1110 => { write!(fmt, "al") }
                    0b0001 => { write!(fmt, "ne") }
                    0b0011 => { write!(fmt, "lo") }
                    0b0101 => { write!(fmt, "pl") }
                    0b0111 => { write!(fmt, "vc") }
                    0b1001 => { write!(fmt, "ls") }
                    0b1011 => { write!(fmt, "lt") }
                    0b1101 => { write!(fmt, "le") }
                    0b1111 => { write!(fmt, "al") }
                    _ => { unreachable!(); }
                }
            }
            Operand::Offset(offs) => {
                if *offs < 0 {
                    write!(fmt, "$-{:#x}", offs.wrapping_neg())
                } else {
                    write!(fmt, "$+{:#x}", offs)
                }
            }
            Operand::PCOffset(offs) => {
                if *offs < 0 {
                    write!(fmt, "$-{:#x}", offs.wrapping_neg())
                } else {
                    write!(fmt, "$+{:#x}", offs)
                }
            }
            Operand::Immediate(i) => {
                write!(fmt, "{:#x}", i)
            },
            Operand::Imm16(i) => {
                write!(fmt, "{:#x}", *i)
            },
            Operand::Imm64(i) => {
                write!(fmt, "{:#x}", *i)
            },
            Operand::ImmShift(i, shift) => {
                match shift {
                    0 => {
                        write!(fmt, "{:#x}", i)
                    },
                    _ => {
                        write!(fmt, "{:#x}, lsl {}", i, shift)
                    }
                }
            },
            Operand::RegShift(shift_type, amount, size, reg) => {
                match size {
                    SizeCode::X => {
                        if *shift_type == ShiftStyle::LSL && *amount == 0 {
                            write!(fmt, "x{}", reg)
                        } else {
                            write!(fmt, "x{}, {} {}", reg, shift_type, amount)
                        }
                    },
                    SizeCode::W => {
                        if *shift_type == ShiftStyle::LSL && *amount == 0 {
                            write!(fmt, "w{}", reg)
                        } else {
                            write!(fmt, "w{}, {} {}", reg, shift_type, amount)
                        }
                    }
                }
            }
            Operand::RegOffset(reg, offset) => {
                if *offset != 0 {
                    if *offset < 0 {
                        write!(fmt, "[{}, -{:#x}]", Operand::RegisterOrSP(SizeCode::X, *reg), -*offset)
                    } else {
                        write!(fmt, "[{}, {:#x}]", Operand::RegisterOrSP(SizeCode::X, *reg), offset)
                    }
                } else {
                    write!(fmt, "[{}]", Operand::RegisterOrSP(SizeCode::X, *reg))
                }
            }
            Operand::RegRegOffset(reg, size_code, index_reg, extend, amount) => {
                match size_code {
                    SizeCode::X => {
                        if *extend == ShiftStyle::LSL && *amount == 0 {
                            write!(fmt, "[x{}, x{}]", reg, index_reg)
                        } else {
                            write!(fmt, "[x{}, x{}, {} {}]", reg, index_reg, extend, amount)
                        }
                    },
                    SizeCode::W => {
                        if *extend == ShiftStyle::LSL && *amount == 0 {
                            write!(fmt, "[x{}, w{}]", reg, index_reg)
                        } else {
                            write!(fmt, "[x{}, w{}, {} {}]", reg, index_reg, extend, amount)
                        }
                    }
                }
            }
            Operand::RegPreIndex(reg, offset) => {
                if *offset != 0 {
                    if *offset < 0 {
                        write!(fmt, "[{}, -{:#x}]!", Operand::RegisterOrSP(SizeCode::X, *reg), -*offset)
                    } else {
                        write!(fmt, "[{}, {:#x}]!", Operand::RegisterOrSP(SizeCode::X, *reg), offset)
                    }
                } else {
                    write!(fmt, "[{}]!", Operand::RegisterOrSP(SizeCode::X, *reg))
                }
            }
            Operand::RegPostIndex(reg, offset) => {
                if *offset != 0 {
                    if *offset < 0 {
                        write!(fmt, "[{}], -{:#x}", Operand::RegisterOrSP(SizeCode::X, *reg), -*offset)
                    } else {
                        write!(fmt, "[{}], {:#x}", Operand::RegisterOrSP(SizeCode::X, *reg), offset)
                    }
                } else {
                    write!(fmt, "[{}]", Operand::RegisterOrSP(SizeCode::X, *reg))
                }
            }
        }
    }
}

#[derive(Default, Debug)]
pub struct InstDecoder {}

#[allow(non_snake_case)]
impl Decoder<ARMv8> for InstDecoder {
    fn decode_into<T: Reader<<ARMv8 as Arch>::Address, <ARMv8 as Arch>::Word>>(&self, inst: &mut Instruction, words: &mut T) -> Result<(), <ARMv8 as Arch>::DecodeError> {
        let mut word_bytes = [0u8; 4];
        words.next_n(&mut word_bytes)?;
        let word = u32::from_le_bytes(word_bytes);


        #[derive(Copy, Clone, Debug)]
        enum Section {
            Unallocated,
            LoadStore,
            DataProcessingReg,
            DataProcessingSimd,
            DataProcessingSimd2,
            DataProcessingImmediate,
            BranchExceptionSystem,
        }

        // from ARM architecture refrence manual for ARMv8, C3.1

        /*
         * ---00---  UNALLOCATED
         * ---100--  Data processing - immediate
         * ---101--  Branch, exception, system instructions
         * ----1-0-  Loads and stores
         * ----101-  Data processing - register
         * ---0111-  Data processing - SIMD and floating point
         * ---1111-  Data processing - SIMD and floating point
         */

        let section_bits = word >> 25;
        let section = [
            Section::Unallocated,                    // 0000
            Section::Unallocated,                    // 0001
            Section::Unallocated,                    // 0010
            Section::Unallocated,                    // 0011
            Section::LoadStore,                      // 0100
            Section::DataProcessingReg,              // 0101
            Section::LoadStore,                      // 0110
            Section::DataProcessingSimd,             // 0111
            Section::DataProcessingImmediate,        // 1000
            Section::DataProcessingImmediate,        // 1001
            Section::BranchExceptionSystem,          // 1010
            Section::BranchExceptionSystem,          // 1011
            Section::LoadStore,                      // 1100
            Section::DataProcessingReg,              // 1101
            Section::LoadStore,                      // 1110
            Section::DataProcessingSimd2,            // 1111
        ][(section_bits & 0x0f) as usize];

        // println!("word: {:#x}, bits: {:#b}", word, section_bits & 0xf);

        match section {
            Section::DataProcessingSimd |
            Section::DataProcessingSimd2 => {
                return Err(DecodeError::IncompleteDecoder);
            }
            Section::Unallocated => {
                inst.opcode = Opcode::Invalid;
            }
            Section::DataProcessingReg => {
                /*
                 * Section C3.5. Data Processing - Register
                 *
                 * instructions here have the form
                 * XXXX101X_XXXXXXXX_XXXXXXXX_XXXXXXXX
                 */
                if (word & 0x10000000) != 0 {
                    // These are of the form
                    // XXX1101X_...
                    let group_bits = (word >> 22) & 0x7;
                    match group_bits {
                        0b000 => {
                            // Add/subtract (with carry)
                            let Rd = (word & 0x1f) as u16;
                            let Rn = ((word >> 5) & 0x1f) as u16;
                            let opc2 = ((word >> 10) & 0x3f) as u16;
                            let Rm = ((word >> 16) & 0x1f) as u16;

                            if opc2 == 0b000000 {
                                inst.opcode = Opcode::Invalid;
                                return Err(DecodeError::InvalidOperand);
                            }

                            let size_code = match word >> 29 {
                                0b000 => {
                                    inst.opcode = Opcode::ADC;
                                    SizeCode::W
                                }
                                0b001 => {
                                    inst.opcode = Opcode::ADCS;
                                    SizeCode::W
                                }
                                0b010 => {
                                    inst.opcode = Opcode::SBC;
                                    SizeCode::W
                                }
                                0b011 => {
                                    inst.opcode = Opcode::SBCS;
                                    SizeCode::W
                                }
                                0b100 => {
                                    inst.opcode = Opcode::ADC;
                                    SizeCode::X
                                }
                                0b101 => {
                                    inst.opcode = Opcode::ADCS;
                                    SizeCode::X
                                }
                                0b110 => {
                                    inst.opcode = Opcode::SBC;
                                    SizeCode::X
                                }
                                0b111 => {
                                    inst.opcode = Opcode::SBCS;
                                    SizeCode::X
                                }
                                _ => {
                                    unreachable!("opc and size flag are three bits");
                                }
                            };

                            inst.operands = [
                                Operand::Register(size_code, Rd),
                                Operand::Register(size_code, Rn),
                                Operand::Register(size_code, Rm),
                                Operand::Nothing
                            ];
                        },
                        0b001 => {
                            // Conditional compare (register/immediate)
                            let imm_or_reg = (word >> 11) & 0x01;

                            let o3 = (word >> 4) & 0x01;
                            let o2 = (word >> 10) & 0x01;
                            let S = (word >> 29) & 0x01;
                            let op = (word >> 30) & 0x01;
                            let sf = (word >> 31) & 0x01;

                            if S != 1 || o2 != 0 || o3 != 0 {
                                inst.opcode = Opcode::Invalid;
                                return Err(DecodeError::InvalidOpcode);
                            }

                            let size = if sf == 1 {
                                SizeCode::X
                            } else {
                                SizeCode::W
                            };

                            inst.opcode = if op == 1 {
                                Opcode::CCMP
                            } else {
                                Opcode::CCMN
                            };

                            let Rn = ((word >> 5) & 0x1f) as u16;
                            let Rm = ((word >> 16) & 0x1f) as u16;
                            let cond = ((word >> 12) & 0x0f) as u8;
                            let nzcv = (word & 0x0f) as u8;

                            inst.operands = [
                                Operand::Register(size, Rn),
                                if imm_or_reg == 1 {
                                    Operand::Immediate(Rm as u32)
                                } else {
                                    Operand::Register(size, Rm)
                                },
                                Operand::Immediate(nzcv as u32),
                                Operand::ConditionCode(cond),
                            ]
                        },
                        0b010 => {
                            // Conditional select
                            let op2 = (word >> 10) & 0x03;
                            let sf_op = (word >> 28) & 0x0c;

                            if word & 0x20000000 != 0 {
                                inst.opcode = Opcode::Invalid;
                                return Err(DecodeError::InvalidOperand);
                            }

                            let size = match sf_op | op2 {
                                0b0000 => {
                                    inst.opcode = Opcode::CSEL;
                                    SizeCode::W
                                },
                                0b0001 => {
                                    inst.opcode = Opcode::CSINC;
                                    SizeCode::W
                                },
                                0b0100 => {
                                    inst.opcode = Opcode::CSINV;
                                    SizeCode::W
                                },
                                0b0101 => {
                                    inst.opcode = Opcode::CSNEG;
                                    SizeCode::W
                                },
                                0b1000 => {
                                    inst.opcode = Opcode::CSEL;
                                    SizeCode::X
                                },
                                0b1001 => {
                                    inst.opcode = Opcode::CSINC;
                                    SizeCode::X
                                },
                                0b1100 => {
                                    inst.opcode = Opcode::CSINV;
                                    SizeCode::X
                                },
                                0b1101 => {
                                    inst.opcode = Opcode::CSNEG;
                                    SizeCode::X
                                },
                                0b0010 |
                                0b0011 |
                                0b0110 |
                                0b0111 |
                                0b1010 |
                                0b1011 |
                                0b1110 |
                                0b1111 => {
                                    inst.opcode = Opcode::Invalid;
                                    return Err(DecodeError::InvalidOpcode);
                                },
                                _ => {
                                    unreachable!("sf, op, op2 are four bits total");
                                }
                            };

                            let Rd = (word & 0x1f) as u16;
                            let Rn = ((word >> 5) & 0x1f) as u16;
                            let Rm = ((word >> 16) & 0x1f) as u16;
                            let cond = ((word >> 12) & 0x0f) as u8;

                            inst.operands = [
                                Operand::Register(size, Rd),
                                Operand::Register(size, Rn),
                                Operand::Register(size, Rm),
                                Operand::ConditionCode(cond)
                            ];
                        },
                        0b011 => {
                            // Data processing (1 source, 2 source)
                            if ((word >> 30) & 1) == 0 {
                                // X0X11010_110XXXXX_XXXXXXXX_XXXXXXXX
                                // Data-processing (2 source)
                                return Err(DecodeError::IncompleteDecoder);
                            } else {
                                // X1X11010_110XXXXX_XXXXXXXX_XXXXXXXX
                                // Data-processing (1 source)
                                let sf = ((word >> 31) & 0x01) as u8;
                                let S = ((word >> 29) & 0x01) as u8;

                                let Rd = (word & 0x1f) as u16;
                                let Rn = ((word >> 5) & 0x1f) as u16;
                                let opcode = ((word >> 10) & 0x3f) as u8;
                                let opcode2 = ((word >> 16) & 0x1f) as u8;
                                // So ARMv8 ARM only says that 0b00000 has well-defined
                                // instructions
                                // however, PAC (added in v8.3) says otherwise.
                                match opcode2 {
                                    0b00000 => {
                                        if S != 0 {
                                            return Err(DecodeError::InvalidOpcode);
                                        }

                                        let (opcode, size) = match (opcode << 1) | sf {
                                            0b000000_0 => (Opcode::RBIT, SizeCode::W),
                                            0b000000_1 => (Opcode::RBIT, SizeCode::X),
                                            0b000001_0 => (Opcode::REV16, SizeCode::W),
                                            0b000001_1 => (Opcode::REV16, SizeCode::X),
                                            0b000010_0 => (Opcode::REV, SizeCode::W),
                                            0b000010_1 => (Opcode::REV32, SizeCode::X),
                                            0b000011_0 => (Opcode::Invalid, SizeCode::W),
                                            0b000011_1 => (Opcode::REV, SizeCode::X),
                                            0b000100_0 => (Opcode::CLZ, SizeCode::W),
                                            0b000100_1 => (Opcode::CLZ, SizeCode::X),
                                            0b000101_0 => (Opcode::CLS, SizeCode::W),
                                            0b000101_1 => (Opcode::CLS, SizeCode::X),
                                            _ => (Opcode::Invalid, SizeCode::W),
                                        };

                                        inst.opcode = opcode;
                                        inst.operands = [
                                            Operand::Register(size, Rd),
                                            Operand::Register(size, Rn),
                                            Operand::Nothing,
                                            Operand::Nothing,
                                        ];

                                        if opcode == Opcode::Invalid {
                                            return Err(DecodeError::InvalidOpcode);
                                        }
                                    }
                                    0b00001 => {
                                        if S != 0 || sf != 1 {
                                            return Err(DecodeError::InvalidOpcode);
                                        }
                                        match opcode {
                                            0b000000 => {
                                                inst.opcode = Opcode::PACIA;
                                                inst.operands = [
                                                    Operand::Register(SizeCode::X, Rd),
                                                    Operand::RegisterOrSP(SizeCode::X, Rn),
                                                    Operand::Nothing,
                                                    Operand::Nothing,
                                                ];
                                            }
                                            0b001000 => {
                                                if Rn != 31 {
                                                    // technically this is undefined - do some
                                                    // cores do something with this?
                                                    inst.opcode = Opcode::Invalid;
                                                    return Err(DecodeError::InvalidOperand);
                                                }
                                                inst.opcode = Opcode::PACIZA;
                                                inst.operands = [
                                                    Operand::Register(SizeCode::X, Rd),
                                                    Operand::Nothing,
                                                    Operand::Nothing,
                                                    Operand::Nothing,
                                                ];
                                            }
                                            _ => {
                                                inst.opcode = Opcode::Invalid;
                                            }
                                        }
                                    }
                                    _ => {
                                        // Data-processing (1 source), op2 > 0b00001 is (currently
                                        // as of v8.3) undefined.
                                        return Err(DecodeError::InvalidOpcode);
                                    }
                                }
                            }
                        },
                        _ => {
                            // Data processing (3 source)
                            let op0 = ((word >> 15) & 0x01) as u8;
                            let op31 = ((word >> 21) & 0x07) as u8;
                            let op54 = ((word >> 29) & 0x03) as u8;
                            let op = op0 | (op31 << 1) | (op54 << 4);
                            let sf = ((word >> 31) & 0x01) as u8;

                            let Rd = ((word >> 0) & 0x1f) as u16;
                            let Rn = ((word >> 5) & 0x1f) as u16;
                            let Ra = ((word >> 10) & 0x1f) as u16;
                            let Rm = ((word >> 16) & 0x1f) as u16;

                            const DATA_PROCESSING_3_SOURCE: &[Result<(Opcode, SizeCode, SizeCode), DecodeError>] = &[
                                Ok((Opcode::MADD, SizeCode::W, SizeCode::W)),
                                Ok((Opcode::MADD, SizeCode::X, SizeCode::X)),
                                Ok((Opcode::MSUB, SizeCode::W, SizeCode::W)),
                                Ok((Opcode::MSUB, SizeCode::X, SizeCode::X)),
                                Err(DecodeError::InvalidOpcode),
                                Ok((Opcode::SMADDL, SizeCode::W, SizeCode::X)),
                                Err(DecodeError::InvalidOpcode),
                                Ok((Opcode::SMSUBL, SizeCode::W, SizeCode::X)),
                                Err(DecodeError::InvalidOpcode),
                                Ok((Opcode::SMULH, SizeCode::W, SizeCode::X)),
                                Err(DecodeError::InvalidOpcode),
                                Err(DecodeError::InvalidOpcode),
                                Err(DecodeError::InvalidOpcode),
                                Err(DecodeError::InvalidOpcode),
                                Err(DecodeError::InvalidOpcode),
                                Err(DecodeError::InvalidOpcode),
                                Err(DecodeError::InvalidOpcode),
                                Err(DecodeError::InvalidOpcode),
                                Err(DecodeError::InvalidOpcode),
                                Err(DecodeError::InvalidOpcode),
                                Err(DecodeError::InvalidOpcode),
                                Ok((Opcode::UMADDL, SizeCode::W, SizeCode::X)),
                                Err(DecodeError::InvalidOpcode),
                                Ok((Opcode::UMSUBL, SizeCode::W, SizeCode::X)),
                                Err(DecodeError::InvalidOpcode),
                                Ok((Opcode::UMULH, SizeCode::X, SizeCode::X)),
                                Err(DecodeError::InvalidOpcode),
                            ];

                            let compound_idx = (op << 1) | sf;
                            crate::armv8::a64::std::eprintln!("word: {:#08x}, compound_idx: {:x}", word, compound_idx);
                            let (opcode, source_size, dest_size) = DATA_PROCESSING_3_SOURCE.get(compound_idx as usize)
                                .map(std::borrow::ToOwned::to_owned)
                                .unwrap_or(Err(DecodeError::InvalidOpcode))?;

                            inst.opcode = opcode;
                            inst.operands = [
                                Operand::Register(dest_size, Rd),
                                Operand::Register(source_size, Rn),
                                Operand::Register(source_size, Rm),
                                Operand::Register(dest_size, Ra), // in practice these match up with the corresponding operand.
                            ];
                            if opcode == Opcode::UMULH {
                                inst.operands[3] = Operand::Nothing;
                            }
                        }
                    }
                } else {
                    // These are of the form
                    // XXX0101X_...
                    // so bits 21 and 24 fully distinguish categories here...
                    // but bit 21 distinguishes between add/sub shifted/extended, which
                    // we can deal with later. so use bit 24 to figure out the instruction
                    // class, first.
                    if (word & 0x01000000) == 0 {
                        // Logical (shifted register)
                        // XXX01010X_...
                        let sf = (word >> 31) == 1;
                        let size = if sf { SizeCode::X } else { SizeCode::W };

                        let opc = (word >> 28) & 6;
                        let n = (word >> 21) & 1;
                        inst.opcode = [
                            Opcode::AND,
                            Opcode::BIC,
                            Opcode::ORR,
                            Opcode::ORN,
                            Opcode::EOR,
                            Opcode::EON,
                            Opcode::ANDS,
                            Opcode::BICS,
                        ][(opc | n) as usize];

                        let shift = ((word >> 22) & 3) as u8;

                        let Rd = (word & 0x1f) as u16;
                        let Rn = ((word >> 5) & 0x1f) as u16;
                        let imm6 = ((word >> 10) & 0x3f) as u8;
                        let Rm = ((word >> 16) & 0x1f) as u16;

                        inst.operands[0] = Operand::Register(size, Rd);
                        inst.operands[1] = Operand::Register(size, Rn);
                        inst.operands[2] = Operand::RegShift(docs::DecodeShift(shift), imm6, size, Rm);
                    } else {
                        // Add/subtract ({shifted,extended} register)
                        // XXX11011X_...
                        // specific instruction is picked by the first two bits..
                        inst.opcode = [
                            Opcode::ADD,
                            Opcode::ADDS,
                            Opcode::SUB,
                            Opcode::SUBS
                        ][((word >> 29) as usize) & 0x03];

                        let sf = (word >> 31) == 1;
                        let size = if sf { SizeCode::X } else { SizeCode::W };

                        // and operands are contingent on bit 21
                        if (word & 0x20_0000) != 0 {
                            // extended form
                            // opt (bits 22, 23) must be 0

                            if (word >> 22) & 0x03 != 0 {
                                inst.opcode = Opcode::Invalid;
                                return Err(DecodeError::InvalidOperand);
                            }

                            let Rd = (word & 0x1f) as u16;
                            let Rn = ((word >> 5) & 0x1f) as u16;
                            let imm3 = (word >> 10) & 0x07;
                            let option = (word >> 13) & 0x07;
                            let Rm = ((word >> 16) & 0x1f) as u16;

                            inst.operands[0] = Operand::Register(size, Rd);
                            inst.operands[1] = Operand::Register(size, Rn);

                            let shift_size = match option {
                                0b011 |
                                0b111 => {
                                    if size == SizeCode::X {
                                        SizeCode::X
                                    } else {
                                        SizeCode::W
                                    }
                                }
                                _ => {
                                    SizeCode::W
                                }
                            };

                            const SHIFT_TYPES: &[ShiftStyle] = &[
                                ShiftStyle::LSL, ShiftStyle::UXTH, ShiftStyle::UXTW, ShiftStyle::UXTX,
                                ShiftStyle::SXTB, ShiftStyle::SXTH, ShiftStyle::SXTW, ShiftStyle::SXTX,
                            ];

                            let shift = imm3 as u8;
                            inst.operands[2] = Operand::RegShift(SHIFT_TYPES[option as usize], shift, shift_size, Rm);
                       } else {
                            // shifted form

                            let shift = (word >> 22) & 0x03;
                            if shift == 0b11 {
                                inst.opcode = Opcode::Invalid;
                                return Err(DecodeError::InvalidOperand);
                            }

                            let Rd = (word & 0x1f) as u16;
                            let Rn = ((word >> 5) & 0x1f) as u16;
                            let imm6 = ((word >> 10) & 0x3f) as u8;
                            let Rm = ((word >> 16) & 0x1f) as u16;

                            if size == SizeCode::W && imm6 >= 32 {
                                inst.opcode = Opcode::Invalid;
                                return Err(DecodeError::InvalidOperand);
                            }

                            inst.operands[0] = Operand::Register(size, Rd);
                            inst.operands[1] = Operand::Register(size, Rn);

                            inst.operands[2] = match shift {
                                0b00 => Operand::RegShift(ShiftStyle::LSL, imm6, size, Rm),
                                0b01 => Operand::RegShift(ShiftStyle::LSR, imm6, size, Rm),
                                0b10 => Operand::RegShift(ShiftStyle::ASR, imm6, size, Rm),
                                _ => { unreachable!("shift is two bits and 0b11 has early test"); },
                            };
                        }
                    }
                }
            },
            Section::DataProcessingImmediate => {
                /*
                 * Section C3.4, Data processing - immediate
                 * This collects bits 23:25, which are the only ones that vary in this category
                 */
                let group_bits = (word >> 23) & 0x7;
                match group_bits {
                    0b000 |
                    0b001 => {
                        // PC-rel addressing
                        if word >= 0x80000000 {
                            inst.opcode = Opcode::ADRP;
                            let offset = (((word >> 3) & 0x1ffffc) | ((word >> 29) & 0x3)) as i32;
                            let extended_offset = (offset << 11) >> 11;
                            inst.operands = [
                                Operand::Register(SizeCode::X, (word & 0x1f) as u16),
                                Operand::Offset((extended_offset as i64) << 12),
                                Operand::Nothing,
                                Operand::Nothing
                            ];
                        } else {
                            inst.opcode = Opcode::ADR;
                            let offset = (((word >> 3) & 0x1ffffc) | ((word >> 29) & 0x3)) as i32;
                            let extended_offset = (offset << 11) >> 11;
                            inst.operands = [
                                Operand::Register(SizeCode::X, (word & 0x1f) as u16),
                                Operand::Offset(extended_offset as i64),
                                Operand::Nothing,
                                Operand::Nothing
                            ];
                        };
                    }
                    0b010 |
                    0b011 => {
                        // add/sub imm
                        let Rd = word & 0x1f;
                        let Rn = (word >> 5) & 0x1f;
                        let imm12 = (word >> 10) & 0xfff;
                        let shift = (word >> 22) & 0x3;
                        let size = match word >> 29 {
                            0b000 => {
                                inst.opcode = Opcode::ADD;
                                SizeCode::W
                            },
                            0b001 => {
                                inst.opcode = Opcode::ADDS;
                                SizeCode::W
                            },
                            0b010 => {
                                inst.opcode = Opcode::SUB;
                                SizeCode::W
                            },
                            0b011 => {
                                inst.opcode = Opcode::SUBS;
                                SizeCode::W
                            },
                            0b100 => {
                                inst.opcode = Opcode::ADD;
                                SizeCode::X
                            },
                            0b101 => {
                                inst.opcode = Opcode::ADDS;
                                SizeCode::X
                            },
                            0b110 => {
                                inst.opcode = Opcode::SUB;
                                SizeCode::X
                            },
                            0b111 => {
                                inst.opcode = Opcode::SUBS;
                                SizeCode::X
                            },
                            _ => {
                                unreachable!("size and opc are three bits");
                            }
                        };
                        if inst.opcode == Opcode::ADD || inst.opcode == Opcode::SUB {
                            inst.operands[0] = Operand::RegisterOrSP(size, Rd as u16);
                        } else {
                            inst.operands[0] = Operand::Register(size, Rd as u16);
                        }
                        inst.operands[1] = Operand::RegisterOrSP(size, Rn as u16);
                        inst.operands[2] = match shift {
                            0b00 => {
                                Operand::Immediate(imm12 as u32)
                            },
                            0b01 => {
                                Operand::Immediate((imm12 << 12) as u32)
                            },
                            0b10 |
                            0b11 => {
                                inst.opcode = Opcode::Invalid;
                                return Err(DecodeError::InvalidOperand);
                            }
                            _ => { unreachable!("shift is two bits"); }
                        };
                        inst.operands[3] = Operand::Nothing;
                    }
                    0b100 => {
                        // logical (imm)
                        let Rd = (word & 0x1f) as u16;
                        let Rn = ((word >> 5) & 0x1f) as u16;
                        let imms = (word >> 10) & 0x3f;
                        let immr = (word >> 16) & 0x3f;
                        let N = (word >> 22) & 1;
                        let size = match word >> 29 {
                            0b000 => {
                                inst.opcode = Opcode::AND;
                                SizeCode::W
                            }
                            0b001 => {
                                inst.opcode = Opcode::ORR;
                                SizeCode::W
                            }
                            0b010 => {
                                inst.opcode = Opcode::EOR;
                                SizeCode::W
                            }
                            0b011 => {
                                inst.opcode = Opcode::ANDS;
                                SizeCode::W
                            }
                            0b100 => {
                                inst.opcode = Opcode::AND;
                                SizeCode::X
                            }
                            0b101 => {
                                inst.opcode = Opcode::ORR;
                                SizeCode::X
                            }
                            0b110 => {
                                inst.opcode = Opcode::EOR;
                                SizeCode::X
                            }
                            0b111 => {
                                inst.opcode = Opcode::ANDS;
                                SizeCode::X
                            }
                            _ => {
                                unreachable!("size and opc are three bits");
                            }
                        };

                        inst.operands = [
                            Operand::Register(size, Rd),
                            Operand::Register(size, Rn),
                            match size {
                                SizeCode::W => Operand::Immediate(docs::DecodeBitMasks_32(N as u8, imms as u8, immr as u8)?.0),
                                SizeCode::X => Operand::Imm64(docs::DecodeBitMasks_64(N as u8, imms as u8, immr as u8)?.0)
                            },
                            Operand::Nothing
                        ];
                    },
                    0b101 => {
                        // move wide (imm)
                        let Rd = word & 0x1f;
                        let imm16 = (word >> 5) & 0xffff;
                        let hw = (word >> 21) & 0x3;
                        let size = match word >> 29 {
                            0b000 => {
                                if hw >= 0x10 {
                                    inst.opcode = Opcode::Invalid;
                                } else {
                                    inst.opcode = Opcode::MOVN;
                                }
                                SizeCode::W
                            },
                            0b001 => {
                                inst.opcode = Opcode::Invalid;
                                SizeCode::W
                            }
                            0b010 => {
                                if hw >= 0x10 {
                                    inst.opcode = Opcode::Invalid;
                                } else {
                                    inst.opcode = Opcode::MOVZ;
                                }
                                SizeCode::W
                            },
                            0b011 => {
                                if hw >= 0x10 {
                                    inst.opcode = Opcode::Invalid;
                                } else {
                                    inst.opcode = Opcode::MOVK;
                                }
                                SizeCode::W
                            },
                            0b100 => {
                                inst.opcode = Opcode::MOVN;
                                SizeCode::X
                            },
                            0b101 => {
                                inst.opcode = Opcode::Invalid;
                                SizeCode::X
                            }
                            0b110 => {
                                inst.opcode = Opcode::MOVZ;
                                SizeCode::X
                            },
                            0b111 => {
                                inst.opcode = Opcode::MOVK;
                                SizeCode::X
                            },
                            _ => {
                                unreachable!("size and opc are three bits");
                            }
                        };

                        inst.operands = [
                            Operand::Register(size, Rd as u16),
                            Operand::ImmShift(imm16 as u16, hw as u8 * 16),
                            Operand::Nothing,
                            Operand::Nothing
                        ];
                    },
                    0b110 => {
                        // bitfield
                        let Rd = word & 0x1f;
                        let Rn = (word >> 5) & 0x1f;
                        let imms = (word >> 10) & 0x3f;
                        let immr = (word >> 16) & 0x3f;
                        let N = (word >> 22) & 0x1;

                        let sf_opc = word >> 29;

                        let size = match sf_opc {
                            0b000 => {
                                if N == 0 {
                                    inst.opcode = Opcode::SBFM;
                                } else {
                                    inst.opcode = Opcode::Invalid;
                                }
                                SizeCode::W
                            }
                            0b001 => {
                                if N == 0 {
                                    inst.opcode = Opcode::BFM;
                                } else {
                                    inst.opcode = Opcode::Invalid;
                                }
                                SizeCode::W
                            }
                            0b010 => {
                                if N == 0 {
                                    inst.opcode = Opcode::UBFM;
                                } else {
                                    inst.opcode = Opcode::Invalid;
                                }
                                SizeCode::W
                            }
                            0b011 => {
                                inst.opcode = Opcode::Invalid;
                                SizeCode::W
                            }
                            0b100 => {
                                if N == 1 {
                                    inst.opcode = Opcode::SBFM;
                                } else {
                                    inst.opcode = Opcode::Invalid;
                                }
                                SizeCode::X
                            }
                            0b101 => {
                                if N == 1 {
                                    inst.opcode = Opcode::BFM;
                                } else {
                                    inst.opcode = Opcode::Invalid;
                                }
                                SizeCode::X
                            }
                            0b110 => {
                                if N == 1 {
                                    inst.opcode = Opcode::UBFM;
                                } else {
                                    inst.opcode = Opcode::Invalid;
                                }
                                SizeCode::X
                            }
                            0b111 => {
                                inst.opcode = Opcode::Invalid;
                                SizeCode::X
                            }
                            _ => {
                                unreachable!("size and opc are three bits");
                            }
                        };

                        inst.operands = [
                            Operand::Register(size, Rd as u16),
                            Operand::Register(size, Rn as u16),
                            Operand::Immediate(immr as u32),
                            Operand::Immediate(imms as u32)
                        ];
                    },
                    0b111 => {
                        // extract
                        // let Rd = word & 0x1f;
                        // let Rn = (word >> 5) & 0x1f;
                        let imms = (word >> 10) & 0x3f;
                        // let Rm = (word >> 16) & 0x1f;
                        let No0 = (word >> 21) & 0x3;

                        let sf_op21 = word >> 29;

                        if sf_op21 == 0b000 {
                            if No0 != 0b00 || imms >= 0x10 {
                                inst.opcode = Opcode::Invalid;
                            } else {
                                inst.opcode = Opcode::EXTR;
                            }
                        } else if sf_op21 == 0b100 {
                            if No0 != 0b10 {
                                inst.opcode = Opcode::Invalid;
                            } else {
                                inst.opcode = Opcode::EXTR;
                            }
                        } else {
                            inst.opcode = Opcode::Invalid;
                        }
                        // eprintln!("decode Rd: {}, Rn: {}, imms: {}, Rm: {}, No0: {}", Rd, Rn, imms, Rm, No0);
                        return Err(DecodeError::IncompleteDecoder);
                    }
                    _ => { unreachable!("group is three bits") }
                }
            },
            Section::LoadStore => {
                /*
                 * This corresponds to section C3.3, Loads and stores.
                 * Specifically, instructions in this category are all of the form
                 *
                 * v _ G G 1 G 0 G G _ v v v v v v _ _ _ _ v v __________
                 *
                 * where G+v variants indicate which instruction class the word is in.
                 *
                 * however! the G bits are sufficient to distinguish most class of instruction.
                 */

                let group_byte = word >> 23;
                let group_bits = (group_byte & 0x03) | ((group_byte >> 1) & 0x04) | ((group_byte >> 2) & 0x18);

                // println!("Group byte: {:#b}, bits: {:#b}", group_byte, group_bits);
                match group_bits {
                    0b00000 => {
                        let Rt = (word & 0x1f) as u16;
                        let Rn = ((word >> 5) & 0x1f) as u16;
                        let Rt2 = ((word >> 10) & 0x1f) as u16;
                        let o0 = (word & 0x0080) >> 7;
                        let Rs = ((word >> 16) & 0x1f) as u16;
                        let Lo1 = (word & 0x600000) >> 21;
                        let size = (word >> 29) & 0x3;
                        // load/store exclusive
                        // o2 == 0
                        inst.opcode = match size {
                            size @ 0b00 |
                            size @ 0b01 => {
                                if Lo1 == 0b00 {
                                    // store ops
                                    inst.operands = [
                                        Operand::Register(SizeCode::W, Rs),
                                        Operand::Register(SizeCode::W, Rt),
                                        Operand::RegisterOrSP(SizeCode::X, Rn),
                                        Operand::Nothing,
                                    ];
                                } else if Lo1 == 0b10 {
                                    // load ops
                                    inst.operands = [
                                        Operand::Register(SizeCode::W, Rt),
                                        Operand::RegisterOrSP(SizeCode::X, Rn),
                                        Operand::Nothing,
                                        Operand::Nothing,
                                    ];
                                } else {
                                    return Err(DecodeError::InvalidOpcode);
                                };
                                if size == 0b00 {
                                    match (Lo1, o0) {
                                        (0b00, 0b0) => Opcode::STXRB,
                                        (0b00, 0b1) => Opcode::STLXRB,
                                        (0b10, 0b0) => Opcode::LDXRB,
                                        (0b10, 0b1) => Opcode::LDAXRB,
                                        _ => {
                                            inst.opcode = Opcode::Invalid;
                                            return Err(DecodeError::InvalidOpcode);
                                        }
                                    }
                                } else if size == 0b01 {
                                    match (Lo1, o0) {
                                        (0b00, 0b0) => Opcode::STXRH,
                                        (0b00, 0b1) => Opcode::STLXRH,
                                        (0b10, 0b0) => Opcode::LDXRH,
                                        (0b10, 0b1) => Opcode::LDAXRH,
                                        _ => {
                                            inst.opcode = Opcode::Invalid;
                                            return Err(DecodeError::InvalidOpcode);
                                        }
                                    }
                                } else {
                                    unreachable!("size was checked to be 0 or 1");
                                }
                            }
                            size @ 0b10 |
                            size @ 0b11 => {
                                let size_code = match size {
                                    0b10 => SizeCode::W,
                                    0b11 => SizeCode::X,
                                    _ => { unreachable!("size is already known to be 0b10 or 0b11"); }
                                };

                                match Lo1 {
                                    0b00 => {
                                        inst.operands = [
                                            Operand::Register(SizeCode::W, Rs),
                                            Operand::Register(size_code, Rt),
                                            Operand::RegisterOrSP(SizeCode::X, Rn), // memory operand?
                                            Operand::Nothing,
                                        ];
                                        match o0 {
                                            0b0 => Opcode::STXR,
                                            0b1 => Opcode::STLXR,
                                            _ => { unreachable!("o0 is one bit"); }
                                        }
                                    }
                                    0b01 => {
                                        inst.operands = [
                                            Operand::Register(SizeCode::W, Rs),
                                            Operand::Register(size_code, Rt),
                                            Operand::Register(size_code, Rt2),
                                            Operand::RegisterOrSP(SizeCode::X, Rn), // memory operand?
                                        ];
                                        match o0 {
                                            0b0 => Opcode::STXP,
                                            0b1 => Opcode::STLXP,
                                            _ => { unreachable!("o0 is one bit"); }
                                        }
                                    }
                                    0b10 => {
                                        inst.operands = [
                                            Operand::Register(size_code, Rt),
                                            Operand::RegisterOrSP(SizeCode::X, Rn), // memory operand?
                                            Operand::Nothing,
                                            Operand::Nothing,
                                        ];
                                        match o0 {
                                            0b0 => Opcode::LDXR,
                                            0b1 => Opcode::LDAXR,
                                            _ => { unreachable!("o0 is one bit"); }
                                        }
                                    }
                                    0b11 => {
                                        inst.operands = [
                                            Operand::Register(size_code, Rt),
                                            Operand::Register(size_code, Rt2),
                                            Operand::RegisterOrSP(SizeCode::X, Rn), // memory operand?
                                            Operand::Nothing,
                                        ];
                                        match o0 {
                                            0b0 => Opcode::LDXP,
                                            0b1 => Opcode::LDAXP,
                                            _ => { unreachable!("o0 is one bit"); }
                                        }
                                    }
                                    _ => { unreachable!("Lo1 is two bits"); }
                                }
                            }
                            _ => {
                                unreachable!("size is two bits");
                            }
                        };
                    },
                    0b00001 => {
                        let Rt = (word & 0x1f) as u16;
                        let Rn = ((word >> 5) & 0x1f) as u16;
                        let _Rt2 = ((word >> 10) & 0x1f) as u16;
                        let o0 = (word >> 15) & 1;
                        let _Rs = (word >> 16) & 0x1f;
                        let Lo1 = (word >> 21) & 0x3;
                        let size = (word >> 30) & 0x3;
                        // load/store exclusive
                        // o2 == 1
                        // STLRB -> Wt (Rt) Xn|SP (Rn)
                        // LDARB -> Wt (Rt) Xn|SP (Rn)
                        // STLRH -> Wt (Rt) Xn|SP (Rn)
                        // LDARH -> Wt (Rt) Xn|SP (Rn)
                        // STLR -> Wt (Rt) Xn|SP (Rn)
                        // LDAR -> Wt (Rt) Xn|SP (Rn)
                        // STLR -> Wt (Rt) Xn|SP (Rn)
                        // LDAR -> Wt (Rt) Xn|SP (Rn)
                        inst.opcode = match (size, Lo1, o0) {
                            (0b00, 0b00, 0b1) => Opcode::STLRB,
                            (0b00, 0b10, 0b1) => Opcode::LDARB,
                            (0b01, 0b00, 0b1) => Opcode::STLRH,
                            (0b01, 0b10, 0b1) => Opcode::LDARH,
                            (0b10, 0b00, 0b1) => Opcode::STLR, // 32-bit
                            (0b10, 0b10, 0b1) => Opcode::LDAR, // 32-bit
                            (0b11, 0b00, 0b1) => Opcode::STLR, // 64-bit
                            (0b11, 0b10, 0b1) => Opcode::LDAR, // 64-bit
                            _ => {
                                inst.opcode = Opcode::Invalid;
                                return Err(DecodeError::InvalidOpcode);
                            }
                        };
                        let size_code = if size == 0b11 {
                            SizeCode::X
                        } else {
                            SizeCode::W
                        };

                        inst.operands = [
                            Operand::Register(size_code, Rt),
                            Operand::RegOffset(Rn, 0),
                            Operand::Nothing,
                            Operand::Nothing,
                        ];
                    },
                    0b01000 |
                    0b01001 => {
                        // load register (literal)
                        // V == 0
                        let opc = (word >> 30) & 0x3;
                        let Rt = (word & 0x1f) as u16;
                        let imm19 = ((((word >> 5) & 0x7ffff) as i32) << 13) >> 13;

                        let size = match opc {
                            0b00 => {
                                inst.opcode = Opcode::LDR;
                                SizeCode::W
                            },
                            0b01 => {
                                inst.opcode = Opcode::LDR;
                                SizeCode::X
                            }
                            0b10 => {
                                inst.opcode = Opcode::LDRSW;
                                SizeCode::W
                            }
                            0b11 => {
                                // PRFM is not supported
                                return Err(DecodeError::IncompleteDecoder);
                            }
                            _ => {
                                unreachable!("opc is two bits");
                            }
                        };

                        inst.operands = [
                            Operand::Register(size, Rt),
                            Operand::PCOffset((imm19 << 2) as i64),
                            Operand::Nothing,
                            Operand::Nothing,
                        ];
                    },
                    0b01100 |
                    0b01101 => {
                        // load register (literal)
                        // V == 1
                        let opc = (word >> 30) & 0x3;
                        let Rt = (word & 0x1f) as u16;
                        let imm19 = ((((word >> 5) & 0x7ffff) as i32) << 13) >> 13;

                        let size_code = match opc {
                            0b00 => SIMDSizeCode::S,
                            0b01 => SIMDSizeCode::D,
                            0b10 => SIMDSizeCode::Q,
                            0b11 => {
                                // 11011100_XXXXXXXX_XXXXXXXX_XXXXXXXX
                                inst.opcode = Opcode::Invalid;
                                return Err(DecodeError::InvalidOpcode);
                            }
                            _ => {
                                unreachable!("opc is two bits");
                            }
                        };

                        inst.opcode = Opcode::LDR;
                        inst.operands = [
                            Operand::SIMDRegister(size_code, Rt),
                            Operand::PCOffset((imm19 << 2) as i64),
                            Operand::Nothing,
                            Operand::Nothing,
                        ];
                    },
                    0b10000 => {
                        // load/store no-allocate pair (offset)
                        // V == 0
                        // let opc_L = ((word >> 22) & 1) | ((word >> 29) & 0x6);
                        // eprintln!("C3.3.7 V==0, opc_L: {}", opc_L);
                        return Err(DecodeError::IncompleteDecoder);
                    },
                    0b10100 => {
                        // load/store no-allocate pair (offset)
                        // V == 1
                        // let opc_L = ((word >> 22) & 1) | ((word >> 29) & 0x6);
                        // eprintln!("C3.3.7 V==1, opc_L: {}", opc_L);
                        return Err(DecodeError::IncompleteDecoder);
                    },
                    0b10001 => {
                        // load/store register pair (post-indexed)
                        // V == 0
                        let Rt = (word & 0x1f) as u16;
                        let Rn = ((word >> 5) & 0x1f) as u16;
                        let Rt2 = ((word >> 10) & 0x1f) as u16;
                        let mut imm7 = ((((word >> 15) & 0x7f) as i16) << 9) >> 9;
                        let opc_L = ((word >> 22) & 1) | ((word >> 29) & 0x6);
                        let size = match opc_L {
                            0b000 => {
                                inst.opcode = Opcode::STP;
                                imm7 <<= 2;
                                SizeCode::W
                            },
                            0b001 => {
                                inst.opcode = Opcode::LDP;
                                imm7 <<= 2;
                                SizeCode::W
                            },
                            0b010 => {
                                inst.opcode = Opcode::Invalid;
                                SizeCode::W
                            },
                            0b011 => {
                                inst.opcode = Opcode::LDPSW;
                                imm7 <<= 2;
                                SizeCode::W
                            },
                            0b100 => {
                                inst.opcode = Opcode::STP;
                                imm7 <<= 3;
                                SizeCode::X
                            },
                            0b101 => {
                                inst.opcode = Opcode::LDP;
                                imm7 <<= 3;
                                SizeCode::X
                            },
                            0b110 |
                            0b111 => {
                                inst.opcode = Opcode::Invalid;
                                SizeCode::X
                            }
                            _ => { unreachable!("opc and L are three bits"); }
                        };
                        inst.operands = [
                            Operand::Register(size, Rt),
                            Operand::Register(size, Rt2),
                            Operand::RegPostIndex(Rn, imm7),
                            Operand::Nothing
                        ];
                    },
                    0b10101 => {
                        // load/store register pair (post-indexed)
                        // V == 1
                        // let opc_L = ((word >> 22) & 1) | ((word >> 29) & 0x6);
                        // eprintln!("C3.3.15 V==1, opc_L: {}", opc_L);
                        return Err(DecodeError::IncompleteDecoder);
                    },
                    0b10010 => {
                        // load/store register pair (offset)
                        // V == 0
                        let Rt = (word & 0x1f) as u16;
                        let Rn = ((word >> 5) & 0x1f) as u16;
                        let Rt2 = ((word >> 10) & 0x1f) as u16;
                        let mut imm7 = ((((word >> 15) & 0x7f) as i16) << 9) >> 9;
                        let opc_L = ((word >> 22) & 1) | ((word >> 29) & 0x6);
                        let size = match opc_L {
                            0b000 => {
                                inst.opcode = Opcode::STP;
                                imm7 <<= 2;
                                SizeCode::W
                            },
                            0b001 => {
                                inst.opcode = Opcode::LDP;
                                imm7 <<= 2;
                                SizeCode::W
                            },
                            0b010 => {
                                inst.opcode = Opcode::Invalid;
                                SizeCode::W
                            },
                            0b011 => {
                                inst.opcode = Opcode::LDPSW;
                                imm7 <<= 2;
                                SizeCode::W
                            },
                            0b100 => {
                                inst.opcode = Opcode::STP;
                                imm7 <<= 3;
                                SizeCode::X
                            },
                            0b101 => {
                                inst.opcode = Opcode::LDP;
                                imm7 <<= 3;
                                SizeCode::X
                            },
                            0b110 |
                            0b111 => {
                                inst.opcode = Opcode::Invalid;
                                SizeCode::X
                            }
                            _ => { unreachable!("opc and L are three bits"); }
                        };
                        inst.operands = [
                            Operand::Register(size, Rt),
                            Operand::Register(size, Rt2),
                            Operand::RegOffset(Rn, imm7),
                            Operand::Nothing
                        ];
                    },
                    0b10110 => {
                        // load/store register pair (offset)
                        // V == 1
                        // let opc_L = ((word >> 22) & 1) | ((word >> 29) & 0x6);
                        // eprintln!("C3.3.14 V==1, opc_L: {}", opc_L);
                        return Err(DecodeError::IncompleteDecoder);
                    },
                    0b10011 => {
                        // load/store register pair (pre-indexed)
                        // V == 0
                        let Rt = (word & 0x1f) as u16;
                        let Rn = ((word >> 5) & 0x1f) as u16;
                        let Rt2 = ((word >> 10) & 0x1f) as u16;
                        let mut imm7 = ((((word >> 15) & 0x7f) as i16) << 9) >> 9;
                        let opc_L = ((word >> 22) & 1) | ((word >> 29) & 0x6);
                        let size = match opc_L {
                            0b000 => {
                                inst.opcode = Opcode::STP;
                                imm7 <<= 2;
                                SizeCode::W
                            },
                            0b001 => {
                                inst.opcode = Opcode::LDP;
                                imm7 <<= 2;
                                SizeCode::W
                            },
                            0b010 => {
                                inst.opcode = Opcode::Invalid;
                                SizeCode::W
                            },
                            0b011 => {
                                inst.opcode = Opcode::LDPSW;
                                imm7 <<= 2;
                                SizeCode::W
                            },
                            0b100 => {
                                inst.opcode = Opcode::STP;
                                imm7 <<= 3;
                                SizeCode::X
                            },
                            0b101 => {
                                inst.opcode = Opcode::LDP;
                                imm7 <<= 3;
                                SizeCode::X
                            },
                            0b110 |
                            0b111 => {
                                inst.opcode = Opcode::Invalid;
                                SizeCode::X
                            }
                            _ => { unreachable!("opc and L are three bits"); }
                        };
                        inst.operands = [
                            Operand::Register(size, Rt),
                            Operand::Register(size, Rt2),
                            Operand::RegPreIndex(Rn, imm7),
                            Operand::Nothing
                        ];
                    },
                    0b10111 => {
                        // load/store register pair (pre-indexed)
                        // V == 1
                        // let opc_L = ((word >> 22) & 1) | ((word >> 29) & 0x6);
                        // eprintln!("C3.3.16 V==1, opc_L: {}", opc_L);
                        return Err(DecodeError::IncompleteDecoder);
                    },
                    0b11000 |
                    0b11001 => {
                        /*
                         * load/store register {unscaled immediate, immediate post-indexed,
                         * unprivileged, immediate pre-indexd, register offset}
                         * V == 0
                         */
                        let Rt = (word & 0x1f) as u16;
                        let Rn = ((word >> 5) & 0x1f) as u16;
                        let size_opc = ((word >> 22) & 0x03) | ((word >> 28) & 0x0c);
                        let category = (word >> 10) & 0x03;
                        // println!("load/store: size_opc: {:#b}, category: {:#b}", size_opc, category);
                        if word & 0x200000 != 0 {
                            match category {
                                0b00 => {
                                    // Atomic memory operations
                                    // V==1
                                    return Err(DecodeError::IncompleteDecoder);
                                }
                                0b01 |
                                0b11 => {
                                    // Load/store register (pac)
                                    // V==1
                                    return Err(DecodeError::IncompleteDecoder);
                                }
                                0b10 => {
                                    // Load/store register (register offset)
                                    // C3.3.10
                                    const OPCODES: &[Result<(Opcode, SizeCode, u8), DecodeError>] = &[
                                        Ok((Opcode::STRB, SizeCode::W, 1)),
                                        Ok((Opcode::LDRB, SizeCode::W, 1)),
                                        Ok((Opcode::LDRSB, SizeCode::X, 1)),
                                        Ok((Opcode::LDRSB, SizeCode::W, 1)),
                                        Ok((Opcode::STRH, SizeCode::W, 1)),
                                        Ok((Opcode::LDRH, SizeCode::W, 1)),
                                        Ok((Opcode::LDRSH, SizeCode::X, 1)),
                                        Ok((Opcode::LDRSH, SizeCode::W, 1)),
                                        Ok((Opcode::STR, SizeCode::W, 2)),
                                        Ok((Opcode::LDR, SizeCode::W, 2)),
                                        Ok((Opcode::LDRSW, SizeCode::X, 2)),
                                        Err(DecodeError::InvalidOpcode),
                                        Ok((Opcode::STR, SizeCode::X, 3)),
                                        Ok((Opcode::LDR, SizeCode::X, 3)),
                                        Err(DecodeError::IncompleteDecoder), // PRFM is not supported yet
                                        Err(DecodeError::InvalidOpcode),
                                    ];

                                    let (opcode, size, shamt) = OPCODES[size_opc as usize]?;
                                    inst.opcode = opcode;

                                    let S = ((word >> 12) & 0x1) as u8;
                                    let option = ((word >> 13) & 0x07) as u8;
                                    let Rm = ((word >> 16) & 0x1f) as u16;

                                    let index_size = match option & 0x3 {
                                        0b00 |
                                        0b01 => {
                                            inst.opcode = Opcode::Invalid;
                                            return Err(DecodeError::InvalidOpcode);
                                        },
                                        0b10 => { SizeCode::W }
                                        0b11 => { SizeCode::X }
                                        _ => { unreachable!("option is two bits"); }
                                    };

                                    const SHIFT_STYLES: &[Result<ShiftStyle, DecodeError>] = &[
                                        Err(DecodeError::InvalidOperand),
                                        Err(DecodeError::InvalidOperand),
                                        Ok(ShiftStyle::UXTW),
                                        Ok(ShiftStyle::LSL),
                                        Err(DecodeError::InvalidOperand),
                                        Err(DecodeError::InvalidOperand),
                                        Ok(ShiftStyle::SXTW),
                                        Ok(ShiftStyle::SXTX),
                                    ];
                                    let shift_style = SHIFT_STYLES[option as usize]?;

                                    inst.operands = [
                                        Operand::Register(size, Rt),
                                        Operand::RegRegOffset(Rn, index_size, Rm, shift_style, S * shamt),
                                        Operand::Nothing,
                                        Operand::Nothing,
                                    ];
                                }
                                _ => {
                                    unreachable!("category is two bits");
                                }
                            }
                        } else {
                            let imm9 = ((((word >> 12) & 0x1ff) as i16) << 7) >> 7;
                            match category {
                                0b00 => {
                                    // Load/store register (unscaled immediate)
                                    const OPCODES: &[Result<(Opcode, SizeCode), DecodeError>] = &[
                                        Ok((Opcode::STURB, SizeCode::W)),
                                        Ok((Opcode::LDURB, SizeCode::W)),
                                        Ok((Opcode::LDURSB, SizeCode::X)),
                                        Ok((Opcode::LDURSB, SizeCode::W)),
                                        Ok((Opcode::STURH, SizeCode::W)),
                                        Ok((Opcode::LDURH, SizeCode::W)),
                                        Ok((Opcode::LDURSH, SizeCode::X)),
                                        Ok((Opcode::LDURSH, SizeCode::W)),
                                        Ok((Opcode::STUR, SizeCode::W)),
                                        Ok((Opcode::LDUR, SizeCode::W)),
                                        Ok((Opcode::LDURSW, SizeCode::X)),
                                        Err(DecodeError::InvalidOpcode),
                                        Ok((Opcode::STUR, SizeCode::X)),
                                        Ok((Opcode::LDUR, SizeCode::X)),
                                        Err(DecodeError::IncompleteDecoder), // PRFM is not supported yet
                                        Err(DecodeError::InvalidOpcode),
                                    ];

                                    let (opcode, size) = OPCODES[size_opc as usize]?;
                                    inst.opcode = opcode;

                                    inst.operands = [
                                        Operand::Register(size, Rt),
                                        Operand::RegOffset(Rn, imm9),
                                        Operand::Nothing,
                                        Operand::Nothing,
                                    ];
                                }
                                0b10 => {
                                    // Load/store register (unprivileged)
                                    const OPCODES: &[Result<(Opcode, SizeCode), DecodeError>] = &[
                                        Ok((Opcode::STTRB, SizeCode::W)),
                                        Ok((Opcode::LDTRB, SizeCode::W)),
                                        Ok((Opcode::LDTRSB, SizeCode::X)),
                                        Ok((Opcode::LDTRSB, SizeCode::W)),
                                        Ok((Opcode::STTRH, SizeCode::W)),
                                        Ok((Opcode::LDTRH, SizeCode::W)),
                                        Ok((Opcode::LDTRSH, SizeCode::X)),
                                        Ok((Opcode::LDTRSH, SizeCode::W)),
                                        Ok((Opcode::STTR, SizeCode::W)),
                                        Ok((Opcode::LDTR, SizeCode::W)),
                                        Ok((Opcode::LDTRSW, SizeCode::X)),
                                        Err(DecodeError::InvalidOpcode),
                                        Ok((Opcode::STUR, SizeCode::X)),
                                        Ok((Opcode::LDTR, SizeCode::X)),
                                        Err(DecodeError::InvalidOpcode),
                                        Err(DecodeError::InvalidOpcode),
                                    ];

                                    let (opcode, size) = OPCODES[size_opc as usize]?;
                                    inst.opcode = opcode;

                                    inst.operands = [
                                        Operand::Register(size, Rt),
                                        Operand::RegPreIndex(Rn, imm9),
                                        Operand::Nothing,
                                        Operand::Nothing,
                                    ];
                                }
                                0b01 |
                                0b11 => {
                                    const OPCODES: &[Result<(Opcode, SizeCode), DecodeError>] = &[
                                        Ok((Opcode::STRB, SizeCode::W)),
                                        Ok((Opcode::LDRB, SizeCode::W)),
                                        Ok((Opcode::LDRSB, SizeCode::X)),
                                        Ok((Opcode::LDRSB, SizeCode::W)),
                                        Ok((Opcode::STRH, SizeCode::W)),
                                        Ok((Opcode::LDRH, SizeCode::W)),
                                        Ok((Opcode::LDRSH, SizeCode::X)),
                                        Ok((Opcode::LDRSH, SizeCode::W)),
                                        Ok((Opcode::STR, SizeCode::W)),
                                        Ok((Opcode::LDR, SizeCode::W)),
                                        Err(DecodeError::InvalidOpcode),
                                        Err(DecodeError::InvalidOpcode),
                                        Ok((Opcode::STR, SizeCode::X)),
                                        Ok((Opcode::LDR, SizeCode::X)),
                                        Err(DecodeError::InvalidOpcode),
                                        Err(DecodeError::InvalidOpcode),
                                    ];

                                    let (opcode, size) = OPCODES[size_opc as usize]?;
                                    inst.opcode = opcode;

                                    inst.operands = [
                                        Operand::Register(size, Rt),
                                        if category == 0b01 {
                                            Operand::RegPostIndex(Rn, imm9)
                                        } else {
                                            Operand::RegPreIndex(Rn, imm9)
                                        },
                                        Operand::Nothing,
                                        Operand::Nothing,
                                    ];
                                },
                                _ => {
                                    unreachable!("category is two bits");
                                }
                            }
                        }
                    }
                    0b11100 |
                    0b11101 => {
                        /*
                         * load/store register {unscaled immediate, immediate post-indexed,
                         * unprivileged, immediate pre-indexd, register offset}
                         * V == 1
                         */
                        return Err(DecodeError::IncompleteDecoder);
                    }
                    0b11010 |
                    0b11011 => {
                        // load/store register (unsigned immediate)
                        // V == 0
                        let Rt = (word & 0x1f) as u16;
                        let Rn = ((word >> 5) & 0x1f) as u16;
                        let imm12 = ((word >> 10) & 0x0fff) as i16;
                        let size_opc = ((word >> 22) & 0x3) | ((word >> 28) & 0xc);
                        match size_opc {
                            0b0000 => {
                                inst.opcode = Opcode::STRB;
                                inst.operands = [
                                    Operand::Register(SizeCode::W, Rt),
                                    Operand::RegOffset(Rn, imm12),
                                    Operand::Nothing,
                                    Operand::Nothing,
                                ];
                            }
                            0b0001 => {
                                inst.opcode = Opcode::LDRB;
                                inst.operands = [
                                    Operand::Register(SizeCode::W, Rt),
                                    Operand::RegOffset(Rn, imm12),
                                    Operand::Nothing,
                                    Operand::Nothing,
                                ];
                            }
                            0b0010 => {
                                inst.opcode = Opcode::LDRSB;
                                inst.operands = [
                                    Operand::Register(SizeCode::X, Rt),
                                    Operand::RegOffset(Rn, imm12),
                                    Operand::Nothing,
                                    Operand::Nothing,
                                ];
                            }
                            0b0011 => {
                                inst.opcode = Opcode::LDRSB;
                                inst.operands = [
                                    Operand::Register(SizeCode::W, Rt),
                                    Operand::RegOffset(Rn, imm12),
                                    Operand::Nothing,
                                    Operand::Nothing,
                                ];
                            }
                            0b0100 => {
                                inst.opcode = Opcode::STRH;
                                inst.operands = [
                                    Operand::Register(SizeCode::W, Rt),
                                    Operand::RegOffset(Rn, imm12 << 1),
                                    Operand::Nothing,
                                    Operand::Nothing,
                                ];
                            }
                            0b0101 => {
                                inst.opcode = Opcode::LDRH;
                                inst.operands = [
                                    Operand::Register(SizeCode::W, Rt),
                                    Operand::RegOffset(Rn, imm12 << 1),
                                    Operand::Nothing,
                                    Operand::Nothing,
                                ];
                            }
                            0b0110 => {
                                inst.opcode = Opcode::LDRSH;
                                inst.operands = [
                                    Operand::Register(SizeCode::X, Rt),
                                    Operand::RegOffset(Rn, imm12 << 1),
                                    Operand::Nothing,
                                    Operand::Nothing,
                                ];
                            }
                            0b0111 => {
                                inst.opcode = Opcode::LDRSH;
                                inst.operands = [
                                    Operand::Register(SizeCode::W, Rt),
                                    Operand::RegOffset(Rn, imm12 << 1),
                                    Operand::Nothing,
                                    Operand::Nothing,
                                ];
                            }
                            0b1000 => {
                                inst.opcode = Opcode::STR;
                                inst.operands = [
                                    Operand::Register(SizeCode::W, Rt),
                                    Operand::RegOffset(Rn, imm12 << 2),
                                    Operand::Nothing,
                                    Operand::Nothing,
                                ];
                            }
                            0b1001 => {
                                inst.opcode = Opcode::LDR;
                                inst.operands = [
                                    Operand::Register(SizeCode::W, Rt),
                                    Operand::RegOffset(Rn, imm12 << 2),
                                    Operand::Nothing,
                                    Operand::Nothing,
                                ];
                            }
                            0b1010 => {
                                inst.opcode = Opcode::LDRSW;
                                inst.operands = [
                                    Operand::Register(SizeCode::X, Rt),
                                    Operand::RegOffset(Rn, imm12 << 2),
                                    Operand::Nothing,
                                    Operand::Nothing,
                                ];
                            }
                            0b1011 => { inst.opcode = Opcode::Invalid; }
                            0b1100 => {
                                inst.opcode = Opcode::STR;
                                inst.operands = [
                                    Operand::Register(SizeCode::X, Rt),
                                    Operand::RegOffset(Rn, imm12 << 3),
                                    Operand::Nothing,
                                    Operand::Nothing,
                                ];
                            }
                            0b1101 => {
                                inst.opcode = Opcode::LDR;
                                inst.operands = [
                                    Operand::Register(SizeCode::X, Rt),
                                    Operand::RegOffset(Rn, imm12 << 3),
                                    Operand::Nothing,
                                    Operand::Nothing,
                                ];
                            }
                            0b1110 => {
                                // PRFM not yet supported
                                return Err(DecodeError::IncompleteDecoder);
                            }
                            0b1111 => { inst.opcode = Opcode::Invalid; }
                            _ => { unreachable!("size and opc are four bits"); }
                        }
                    },
                    0b11110 |
                    0b11111 => {
                        // load/store register (unsigned immediate)
                        // V == 1
                        return Err(DecodeError::IncompleteDecoder);
                    },
                    0b00100 => {
                        // AdvSIMD load/store multiple structures
                        return Err(DecodeError::IncompleteDecoder);
                    },
                    0b00101 => {
                        // AdvSIMD load/store multiple structures (post-indexed)
                        return Err(DecodeError::IncompleteDecoder);
                    },
                    0b00110 => {
                        // AdvSIMD load/store single structure
                        return Err(DecodeError::IncompleteDecoder);
                    },
                    0b00111 => {
                        // AdvSIMD load/store single structure (post-indexed)
                        return Err(DecodeError::IncompleteDecoder);
                    }
                    _ => {
                        inst.opcode = Opcode::Invalid;
                    }
                }
            },
            Section::BranchExceptionSystem => {
                let group_bits = ((word >> 29) << 2) | ((word >> 24) & 0x03);
                match group_bits {
                    0b00000 |
                    0b00001 |
                    0b00010 |
                    0b00011 => { // unconditional branch (imm)
                        let offset = ((word & 0x03ff_ffff) << 2) as i32;
                        let extended_offset = (offset << 4) >> 4;
                        inst.opcode = Opcode::B;
                        inst.operands = [
                            Operand::Offset(extended_offset as i64),
                            Operand::Nothing,
                            Operand::Nothing,
                            Operand::Nothing
                        ];
                    },
                    0b00100 => { // compare branch (imm)
                        inst.opcode = Opcode::CBZ;
                        let offset = (word as i32 & 0x00ff_ffe0) >> 3;
                        let extended_offset = (offset << 11) >> 11;
                        let Rt = word & 0x1f;
                        inst.operands = [
                            Operand::Register(SizeCode::W, Rt as u16),
                            Operand::Offset(extended_offset as i64),
                            Operand::Nothing,
                            Operand::Nothing
                        ];
                    },
                    0b00101 => { // compare branch (imm)
                        inst.opcode = Opcode::CBNZ;
                        let offset = (word as i32 & 0x00ff_ffe0) >> 3;
                        let extended_offset = (offset << 11) >> 11;
                        let Rt = word & 0x1f;
                        inst.operands = [
                            Operand::Register(SizeCode::W, Rt as u16),
                            Operand::Offset(extended_offset as i64),
                            Operand::Nothing,
                            Operand::Nothing
                        ];
                    },
                    0b00110 => { // test branch (imm)
                        let offset = (word as i32 & 0x0007_ffe0) >> 3;
                        let extended_offset = (offset << 16) >> 16;
                        let b = (word >> 19) & 0x1f;
                        let Rt = word & 0x1f;
                        inst.opcode = Opcode::TBZ;
                        inst.operands = [
                            Operand::Register(SizeCode::W, Rt as u16),
                            Operand::Imm16(b as u16),
                            Operand::Offset(extended_offset as i64),
                            Operand::Nothing
                        ];
                    },
                    0b00111 => { // test branch (imm)
                        let offset = (word as i32 & 0x0007_ffe0) >> 3;
                        let extended_offset = (offset << 16) >> 16;
                        let b = (word >> 19) & 0x1f;
                        let Rt = word & 0x1f;
                        inst.opcode = Opcode::TBNZ;
                        inst.operands = [
                            Operand::Register(SizeCode::W, Rt as u16),
                            Operand::Imm16(b as u16),
                            Operand::Offset(extended_offset as i64),
                            Operand::Nothing
                        ];
                    },
                    0b01000 => { // conditional branch (imm)
                        let offset = (word as i32 & 0x00ff_ffe0) >> 3;
                        let extended_offset = (offset << 11) >> 11;
                        let cond = word & 0x0f;
                        inst.opcode = Opcode::Bcc(cond as u8);
                        inst.operands = [
                            Operand::Offset(extended_offset as i64),
                            Operand::Nothing,
                            Operand::Nothing,
                            Operand::Nothing
                        ];
                    }
                    0b01001 => { // conditional branch (imm)
                        return Err(DecodeError::IncompleteDecoder);
                        inst.opcode = Opcode::Invalid;
                    }
                    /* 0b01010 to 0b01111 seem all invalid? */
                    0b10000 |
                    0b10001 |
                    0b10010 |
                    0b10011 => { // unconditional branch (imm)
                        let offset = ((word & 0x03ff_ffff) << 2) as i32;
                        let extended_offset = (offset << 4) >> 4;
                        inst.opcode = Opcode::BL;
                        inst.operands = [
                            Operand::Offset(extended_offset as i64),
                            Operand::Nothing,
                            Operand::Nothing,
                            Operand::Nothing
                        ];
                    },
                    0b10100 => { // compare branch (imm)
                        inst.opcode = Opcode::CBZ;
                        let offset = (word as i32 & 0x00ff_ffe0) >> 3;
                        let extended_offset = (offset << 11) >> 11;
                        let Rt = word & 0x1f;
                        inst.operands = [
                            Operand::Register(SizeCode::X, Rt as u16),
                            Operand::Offset(extended_offset as i64),
                            Operand::Nothing,
                            Operand::Nothing
                        ];
                    },
                    0b10101 => { // compare branch (imm)
                        inst.opcode = Opcode::CBNZ;
                        let offset = (word as i32 & 0x00ff_ffe0) >> 3;
                        let extended_offset = (offset << 11) >> 11;
                        let Rt = word & 0x1f;
                        inst.operands = [
                            Operand::Register(SizeCode::X, Rt as u16),
                            Operand::Offset(extended_offset as i64),
                            Operand::Nothing,
                            Operand::Nothing
                        ];
                    },
                    0b10110 => { // test branch (imm)
                        let offset = (word as i32 & 0x0007_ffe0) >> 3;
                        let extended_offset = (offset << 16) >> 16;
                        let b = (word >> 19) & 0x1f;
                        let Rt = word & 0x1f;
                        inst.opcode = Opcode::TBZ;
                        inst.operands = [
                            Operand::Register(SizeCode::X, Rt as u16),
                            Operand::Imm16((b as u16) | 0x20),
                            Operand::Offset(extended_offset as i64),
                            Operand::Nothing
                        ];
                    },
                    0b10111 => { // test branch (imm)
                        let offset = (word as i32 & 0x0007_ffe0) >> 3;
                        let extended_offset = (offset << 16) >> 16;
                        let b = (word >> 19) & 0x1f;
                        let Rt = word & 0x1f;
                        inst.opcode = Opcode::TBNZ;
                        inst.operands = [
                            Operand::Register(SizeCode::X, Rt as u16),
                            Operand::Imm16((b as u16) | 0x20),
                            Operand::Offset(extended_offset as i64),
                            Operand::Nothing
                        ];
                    },
                    0b11000 => { // exception generation
                        let ll = word & 0x3;
                        let op2 = (word >> 2) & 0x7;
                        let opc = (word >> 21) & 0x7;
                        match (opc, op2, ll) {
                            (0b000, 0b000, 0b01) => {
                                inst.opcode = Opcode::SVC;
                            }
                            (0b000, 0b000, 0b10) => {
                                inst.opcode = Opcode::HVC;
                            }
                            (0b000, 0b000, 0b11) => {
                                inst.opcode = Opcode::SMC;
                            }
                            (0b001, 0b000, 0b00) => {
                                inst.opcode = Opcode::BRK;
                            }
                            (0b010, 0b000, 0b00) => {
                                inst.opcode = Opcode::HLT;
                            }
                            (0b101, 0b000, 0b01) => {
                                inst.opcode = Opcode::DCPS1;
                            }
                            (0b101, 0b000, 0b10) => {
                                inst.opcode = Opcode::DCPS2;
                            }
                            (0b101, 0b000, 0b11) => {
                                inst.opcode = Opcode::DCPS3;
                            }
                            _ => {
                                inst.opcode = Opcode::Invalid;
                            }
                        }
                        let imm = (word >> 5) & 0xffff;
                        inst.operands = [
                            Operand::Imm16(imm as u16),
                            Operand::Nothing,
                            Operand::Nothing,
                            Operand::Nothing
                        ];
                    },
                    0b11001 => { // system
                        let remainder = word & 0xffffff;
                        if remainder >= 0x400000 {
                            inst.opcode = Opcode::Invalid;
                        } else {
                            let Rt = word & 0x1f;
                            let Lop0 = ((word >> 19) & 0x7) as u8;
                            match Lop0 {
                                0b000 => {
                                    // MSR, HINT, CLREX, DSB, DMB, ISB
                                    if Rt == 0b11111 {
                                        let CRn = (word >> 12) & 0xf;
                                        let op1 = (word >> 16) & 0x7;
                                        let op2 = (word >> 5) & 0x1f;

                                        match CRn {
                                            0b0010 => {
                                                if op1 == 0b011 {
                                                    inst.opcode = Opcode::HINT(op2 as u8);
                                                } else {
                                                    inst.opcode = Opcode::Invalid;
                                                }
                                            },
                                            0b0011 => {
                                                match op2 {
                                                    0b010 => {
                                                        inst.opcode = Opcode::CLREX;
                                                    },
                                                    0b100 => {
                                                        inst.opcode = Opcode::DSB;
                                                    },
                                                    0b101 => {
                                                        inst.opcode = Opcode::DMB;
                                                    },
                                                    0b110 => {
                                                        inst.opcode = Opcode::ISB;
                                                    }
                                                    _ => {
                                                        inst.opcode = Opcode::Invalid;
                                                    }
                                                };
                                            },
                                            0b0100 => {
                                                inst.opcode = Opcode::MSRa(op1 as u8, op2 as u8);
                                                inst.operands[0] = Operand::Imm16(
                                                    ((word >> 8) & 0xf) as u16
                                                );
                                            }
                                            _ => {
                                                inst.opcode = Opcode::Invalid;
                                            }
                                        }
                                    } else {
                                        inst.opcode = Opcode::Invalid;
                                    }
                                }
                                0b001 => {
                                    inst.opcode = Opcode::SYS;
                                    return Err(DecodeError::IncompleteDecoder);
                                }
                                0b010 |
                                0b011 => {
                                    inst.opcode = Opcode::MSRb(word & 0x0fffff);
                                }
                                0b100 => {
                                    inst.opcode = Opcode::Invalid;
                                }
                                0b101 => {
                                    inst.opcode = Opcode::SYSL;
                                    return Err(DecodeError::IncompleteDecoder);
                                }
                                0b110 |
                                0b111 => {
                                    inst.opcode = Opcode::MRS(word & 0x0fffff);
                                }
                                _ => {
                                    inst.opcode = Opcode::Invalid;
                                }
                            }
                        }
                    },
                    0b11010 => { // unconditional branch (reg)
                        // actually the low 3 bits of opc
                        let opc = (word >> 21) & 0x7;
                        match opc {
                            0b000 => {
                                if (word & 0x1ffc1f) == 0x1f0000 {
                                    let Rn = (word >> 5) & 0x1f;
                                    inst.opcode = Opcode::BR;
                                    inst.operands = [
                                        Operand::Register(SizeCode::X, Rn as u16),
                                        Operand::Nothing,
                                        Operand::Nothing,
                                        Operand::Nothing
                                    ];
                                } else {
                                    inst.opcode = Opcode::Invalid;
                                }
                            },
                            0b001 => {
                                if (word & 0x1ffc1f) == 0x1f0000 {
                                    let Rn = (word >> 5) & 0x1f;
                                    inst.opcode = Opcode::BLR;
                                    inst.operands = [
                                        Operand::Register(SizeCode::X, Rn as u16),
                                        Operand::Nothing,
                                        Operand::Nothing,
                                        Operand::Nothing
                                    ];
                                } else {
                                    inst.opcode = Opcode::Invalid;
                                }
                            },
                            0b010 => {
                                if (word & 0x1ffc1f) == 0x1f0000 {
                                    let Rn = (word >> 5) & 0x1f;
                                    inst.opcode = Opcode::RET;
                                    inst.operands = [
                                        Operand::Register(SizeCode::X, Rn as u16),
                                        Operand::Nothing,
                                        Operand::Nothing,
                                        Operand::Nothing
                                    ];
                                } else {
                                    inst.opcode = Opcode::Invalid;
                                }
                            },
                            0b100 => {
                                if (word & 0x1fffff) == 0x1f03e0 {
                                    inst.opcode = Opcode::ERET;
                                } else {
                                    inst.opcode = Opcode::Invalid;
                                }
                            },
                            0b101 => {
                                if (word & 0x1fffff) == 0x1f03e0 {
                                    inst.opcode = Opcode::DRPS;
                                } else {
                                    inst.opcode = Opcode::Invalid;
                                }
                            },
                            _ => {
                                inst.opcode = Opcode::Invalid;
                            }
                        }
                    }
                    0b11011 => { // unconditional branch (reg)
                        // the last 1 is bit 24, which C3.2.7 indicates are
                        // all invalid encodings (opc is b0101 or lower)
                        inst.opcode = Opcode::Invalid;
                    }
                    _ => {
                        // TODO: invalid
                        return Err(DecodeError::InvalidOpcode);
                    }
                }
            },
        };

        Ok(())
    }
}
