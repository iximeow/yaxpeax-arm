//#[cfg(feature="use-serde")]
//use serde::{Serialize, Deserialize};

use std::fmt::{Display, Formatter};

use yaxpeax_arch::{Arch, Colorize, Colored, ColorSettings, Decoder, LengthedInstruction, ShowContextual, YaxColors};

struct ConditionedOpcode(pub Opcode, pub ConditionCode);

impl Display for ConditionedOpcode {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{}{}", self.0, self.1)
    }
}

#[allow(non_snake_case)]
impl <T: std::fmt::Write> ShowContextual<u32, [Option<String>], T> for Instruction {
    fn contextualize(&self, colors: Option<&ColorSettings>, _address: u32, _context: Option<&[Option<String>]>, out: &mut T) -> std::fmt::Result {
        match self.opcode {
            Opcode::LDR(true, false, false) => {
                match self.operands {
                    Operands::TwoRegImm(13, Rt, 4) => {
                        ConditionedOpcode(Opcode::POP, self.condition).colorize(colors, out)?;
                        return write!(out, " {{{}}}", reg_name_colorize(Rt, colors));
                    },
                    _ => {}
                }
            },
            Opcode::STR(false, true, true) => {
                match self.operands {
                    Operands::TwoRegImm(13, Rt, 4) => {
                        ConditionedOpcode(Opcode::PUSH, self.condition).colorize(colors, out)?;
                        return write!(out, " {{{}}}", reg_name_colorize(Rt, colors));
                    },
                    _ => {}
                }
            },
            Opcode::LDM(true, false, true, _usermode) => {
                // TODO: what indicates usermode in the ARM syntax?
                match self.operands {
                    Operands::RegRegList(13, list) => {
                        ConditionedOpcode(Opcode::POP, self.condition).colorize(colors, out)?;
                        write!(out, " ")?;
                        return format_reg_list(out, list, colors);
                    }
                    _ => {}
                }
            }
            Opcode::STM(false, true, true, _usermode) => {
                // TODO: what indicates usermode in the ARM syntax?
                match self.operands {
                    Operands::RegRegList(13, list) => {
                        ConditionedOpcode(Opcode::PUSH, self.condition).colorize(colors, out)?;
                        write!(out, " ")?;
                        return format_reg_list(out, list, colors);
                    }
                    _ => {}
                }
            }
            _ => {}
        }

        match self.opcode {
            Opcode::LDR(add, pre, wback) |
            Opcode::STR(add, pre, wback) |
            Opcode::STRB(add, pre, wback) |
            Opcode::LDRB(add, pre, wback) => {
                match self.operands {
                    Operands::TwoRegImm(Rn, Rt, imm) => {
                        ConditionedOpcode(self.opcode, self.condition).colorize(colors, out)?;
                        write!(
                            out, " {}, ",
                            reg_name_colorize(Rt, colors),
                        )?;
                        return format_reg_imm_mem(out, Rn, imm, add, pre, wback, colors);
                    }
                    // TODO: this might not be necessary
                    Operands::RegImm(Rt, imm) => {
                        ConditionedOpcode(self.opcode, self.condition).colorize(colors, out)?;
                        write!(
                            out, " {}, ",
                            reg_name_colorize(Rt, colors)
                        )?;
                        return format_reg_imm_mem(out, 15, imm, add, pre, wback, colors);
                    },
                    Operands::ThreeOperandWithShift(Rd, Rn, Rm, shift) => {
                        ConditionedOpcode(self.opcode, self.condition).colorize(colors, out)?;
                        write!(
                            out, " {}, ",
                            reg_name_colorize(Rn, colors)
                        )?;
                        return format_reg_shift_mem(out, Rd, Rm, shift, add, pre, wback, colors);
                    }
                    _ => { unreachable!(); }
                }
            }
            // TODO: [add, pre, usermode]
            Opcode::STM(_add, _pre, wback, _usermode) |
            Opcode::LDM(_add, _pre, wback, _usermode) => {
                match self.operands {
                    Operands::RegRegList(Rr, list) => {
                        ConditionedOpcode(self.opcode, self.condition).colorize(colors, out)?;
                        write!(
                            out, " {}{}, ",
                            reg_name_colorize(Rr, colors),
                            if wback { "!" } else { "" }
                        )?;
                        return format_reg_list(out, list, colors);
                    },
                    _ => { unreachable!(); }
                }
            },
            Opcode::Incomplete(word) => {
                write!(out, "incomplete: {:#x}", word)
            },
            _ => {
                ConditionedOpcode(self.opcode, self.condition).colorize(colors, out)?;
                match self.operands {
                    Operands::RegisterList(list) => {
                        write!(out, " ")?;
                        format_reg_list(out, list, colors)?;
                    },
                    Operands::OneOperand(a) => {
                        write!(out, " {}", reg_name_colorize(a, colors))?;
                    },
                    Operands::TwoOperand(a, b) => {
                        write!(out, " {}, {}", reg_name_colorize(a, colors), reg_name_colorize(b, colors))?;
                    },
                    Operands::RegImm(a, imm) => {
                        write!(out, " {}, {:#x}", reg_name_colorize(a, colors), imm)?;
                    },
                    Operands::RegRegList(r, list) => {
                        write!(out, " {}, ", reg_name_colorize(r, colors))?;
                        format_reg_list(out, list, colors)?;
                    },
                    Operands::TwoRegImm(_a, _b, _imm) => {
                        // TODO:
                        write!(out, " <unimplemented>")?;
                    },
                    Operands::ThreeOperand(a, b, c) => {
                        write!(out, " {}, {}, {}", reg_name_colorize(a, colors), reg_name_colorize(b, colors), reg_name_colorize(c, colors))?;
                    },
                    Operands::ThreeOperandImm(_a, _b, _imm) => {
                        // TODO:
                        write!(out, " <unimplemented>")?;
                    },
                    Operands::ThreeOperandWithShift(a, b, c, shift) => {
                        write!(out, " {}, {}, ", reg_name_colorize(a, colors), reg_name_colorize(b, colors))?;
                        format_shift(out, c, shift, colors)?;
                    },
                    Operands::MulThreeRegs(a, b, c) => {
                        write!(out, " {}, {}, {}", reg_name_colorize(a, colors), reg_name_colorize(b, colors), reg_name_colorize(c, colors))?;
                    },
                    Operands::MulFourRegs(_a, _b, _c, _d) => {
                        // TODO:
                        write!(out, " <unimplemented>")?;
                    },
                    Operands::BranchOffset(imm) => {
                        if imm < 0 {
                            write!(out, " $-{:#x}", (-imm) * 4)?;
                        } else {
                            write!(out, " $+{:#x}", imm * 4)?;
                        }
                    }
                };
                Ok(())
            }
        }
    }
}

impl <T: std::fmt::Write> Colorize<T> for ConditionedOpcode {
    fn colorize(&self, colors: Option<&ColorSettings>, out: &mut T) -> std::fmt::Result {
        match self.0 {
            Opcode::Incomplete(_) |
            Opcode::Invalid => { write!(out, "{}", colors.invalid_op(self)) },
            Opcode::B |
            Opcode::BL |
            Opcode::BLX |
            Opcode::BX |
            Opcode::BXJ => { write!(out, "{}", colors.control_flow_op(self)) },

            Opcode::AND |
            Opcode::EOR |
            Opcode::ORR |
            Opcode::LSL |
            Opcode::LSR |
            Opcode::ROR |
            Opcode::ASR |
            Opcode::RRX |
            Opcode::BIC |

            Opcode::ADR |
            Opcode::SUB |
            Opcode::RSB |
            Opcode::ADD |
            Opcode::ADC |
            Opcode::SBC |
            Opcode::RSC |

            Opcode::MUL |
            Opcode::MLA |
            Opcode::UMAAL |
            Opcode::MLS |
            Opcode::UMULL |
            Opcode::UMLAL |
            Opcode::SMULL |
            Opcode::SMLAL => { write!(out, "{}", colors.arithmetic_op(self)) },

            Opcode::PUSH |
            Opcode::POP => { write!(out, "{}", colors.stack_op(self)) },

            Opcode::TST |
            Opcode::TEQ |
            Opcode::CMP |
            Opcode::CMN => { write!(out, "{}", colors.comparison_op(self)) },

            Opcode::LDREXH |
            Opcode::STREXH |
            Opcode::LDREXB |
            Opcode::STREXB |
            Opcode::LDREXD |
            Opcode::STREXD |
            Opcode::LDREX |
            Opcode::STREX |
            Opcode::LDM(false, false, _, _) |
            Opcode::LDM(false, true, _, _) |
            Opcode::LDM(true, false, _, _) |
            Opcode::LDM(true, true, _, _) |
            Opcode::STM(false, false, _, _) |
            Opcode::STM(false, true, _, _) |
            Opcode::STM(true, false, _, _) |
            Opcode::STM(true, true, _, _) |
            Opcode::LDR(_, _, _) |
            Opcode::STR(_, _, _) |
            Opcode::LDRB(_, _, _) |
            Opcode::STRB(_, _, _) |
            Opcode::LDRT(_) |
            Opcode::STRT(_) |
            Opcode::LDRBT(_) |
            Opcode::STRBT(_) |
            Opcode::SWP |
            Opcode::SWPB |
            Opcode::MOV |
            Opcode::MVN => { write!(out, "{}", colors.data_op(self)) },
        }
    }
}

impl Display for Opcode {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        match self {
            Opcode::Incomplete(word) => { write!(f, "incomplete: {:#x}", word) },
            Opcode::Invalid => { write!(f, "invalid") },
            Opcode::POP => { write!(f, "pop") },
            Opcode::PUSH => { write!(f, "push") },
            Opcode::B => { write!(f, "b") },
            Opcode::BL => { write!(f, "bl") },
            Opcode::BLX => { write!(f, "blx") },
            Opcode::BX => { write!(f, "bx") },
            Opcode::BXJ => { write!(f, "bxj") },
            Opcode::AND => { write!(f, "and") },
            Opcode::EOR => { write!(f, "eor") },
            Opcode::SUB => { write!(f, "sub") },
            Opcode::RSB => { write!(f, "rsb") },
            Opcode::ADD => { write!(f, "add") },
            Opcode::ADC => { write!(f, "adc") },
            Opcode::SBC => { write!(f, "sbc") },
            Opcode::RSC => { write!(f, "rsc") },
            Opcode::TST => { write!(f, "tst") },
            Opcode::TEQ => { write!(f, "teq") },
            Opcode::CMP => { write!(f, "cmp") },
            Opcode::CMN => { write!(f, "cmn") },
            Opcode::ORR => { write!(f, "orr") },
            Opcode::MOV => { write!(f, "mov") },
            Opcode::BIC => { write!(f, "bic") },
            Opcode::MVN => { write!(f, "mvn") },
            Opcode::LSL => { write!(f, "lsl") },
            Opcode::LSR => { write!(f, "lsr") },
            Opcode::ASR => { write!(f, "asr") },
            Opcode::RRX => { write!(f, "rrx") },
            Opcode::ROR => { write!(f, "ror") },
            Opcode::ADR => { write!(f, "adr") },
            Opcode::LDREXH => { write!(f, "ldrexh") },
            Opcode::STREXH => { write!(f, "strexh") },
            Opcode::LDREXB => { write!(f, "ldrexb") },
            Opcode::STREXB => { write!(f, "strexb") },
            Opcode::LDREXD => { write!(f, "ldrexd") },
            Opcode::STREXD => { write!(f, "strexd") },
            Opcode::LDREX => { write!(f, "ldrex") },
            Opcode::STREX => { write!(f, "strex") },
            Opcode::LDM(false, false, _, _) => { write!(f, "ldmda") },
            Opcode::LDM(false, true, _, _) => { write!(f, "ldmdb") },
            Opcode::LDM(true, false, _, _) => { write!(f, "ldm") },
            Opcode::LDM(true, true, _, _) => { write!(f, "ldmia") },
            Opcode::STM(false, false, _, _) => { write!(f, "stmda") },
            Opcode::STM(false, true, _, _) => { write!(f, "stmdb") },
            Opcode::STM(true, false, _, _) => { write!(f, "stm") },
            Opcode::STM(true, true, _, _) => { write!(f, "stmia") },
            Opcode::LDR(_, _, _) => { write!(f, "ldr") },
            Opcode::STR(_, _, _) => { write!(f, "str") },
            Opcode::LDRB(_, _, _) => { write!(f, "ldrb") },
            Opcode::STRB(_, _, _) => { write!(f, "strb") },
            Opcode::LDRT(_) => { write!(f, "ldrt") },
            Opcode::STRT(_) => { write!(f, "strt") },
            Opcode::LDRBT(_) => { write!(f, "ldrbt") },
            Opcode::STRBT(_) => { write!(f, "strbt") },
            Opcode::SWP => { write!(f, "swp") },
            Opcode::SWPB => { write!(f, "swpb") },
            Opcode::MUL => { write!(f, "mul") },
            Opcode::MLA => { write!(f, "mla") },
            Opcode::UMAAL => { write!(f, "umaal") },
            Opcode::MLS => { write!(f, "mls") },
            Opcode::UMULL => { write!(f, "umull") },
            Opcode::UMLAL => { write!(f, "umlal") },
            Opcode::SMULL => { write!(f, "smull") },
            Opcode::SMLAL => { write!(f, "smlal") }
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Opcode {
    Incomplete(u32),
    Invalid,
    /*
     * These two don't really have direct encodings, but are for the specific instances
     * where the semantics of the original instruction are the same as push (specifically
     * ldm/stm/mov that write to the stack and increment/decrement appropriately
     */
    POP,
    PUSH,

    B,
    BL,
    BLX,
    BX,
    BXJ,
    AND,
    EOR,
    SUB,
    RSB,
    ADD,
    ADC,
    SBC,
    RSC,
    TST,
    TEQ,
    CMP,
    CMN,
    ORR,
    MOV,
    BIC,
    MVN,
    LSL,
    LSR,
    ASR,
    RRX,
    ROR,
    ADR,
    LDREXH,
    STREXH,
    LDREXB,
    STREXB,
    LDREXD,
    STREXD,
    LDREX,
    STREX,
    LDM(bool, bool, bool, bool),
    STM(bool, bool, bool, bool),
    LDR(bool, bool, bool),
    STR(bool, bool, bool),
    LDRB(bool, bool, bool),
    STRB(bool, bool, bool),
    LDRT(bool),
    STRT(bool),
    LDRBT(bool),
    STRBT(bool),
    SWP,
    SWPB,
    MUL,
    MLA,
    UMAAL,
    MLS,
    UMULL,
    UMLAL,
    SMULL,
    SMLAL
}

static DATA_PROCESSING_OPCODES: [Opcode; 16] = [
    Opcode::AND,
    Opcode::EOR,
    Opcode::SUB,
    Opcode::RSB,
    Opcode::ADD,
    Opcode::ADC,
    Opcode::SBC,
    Opcode::RSC,
    Opcode::TST,
    Opcode::TEQ,
    Opcode::CMP,
    Opcode::CMN,
    Opcode::ORR,
    Opcode::MOV,
    Opcode::BIC,
    Opcode::MVN
];

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum ShiftSpec {
    Immediate(u8),
    Register(u8)
}

#[derive(Debug, PartialEq, Eq)]
pub enum Operands {
    RegisterList(u16),
    OneOperand(u8),
    TwoOperand(u8, u8),
    RegImm(u8, u32),
    RegRegList(u8, u16),
    TwoRegImm(u8, u8, u32),
    ThreeOperand(u8, u8, u8),
    ThreeOperandImm(u8, u8, u16),
    ThreeOperandWithShift(u8, u8, u8, ShiftSpec),
    MulThreeRegs(u8, u8, u8),
    MulFourRegs(u8, u8, u8, u8),
    BranchOffset(i32)
}

#[derive(Debug, PartialEq, Eq)]
pub struct Instruction {
    pub condition: ConditionCode,
    pub opcode: Opcode,
    pub operands: Operands,
    pub s: bool
}

#[allow(non_snake_case)]
impl Instruction {
    pub fn blank() -> Instruction {
        Instruction {
            condition: ConditionCode::AL,
            opcode: Opcode::Invalid,
            operands: Operands::BranchOffset(0),
            s: false
        }
    }
    pub fn set_S(&mut self, value: bool) {
        self.s = value;
    }
    pub fn S(&self) -> bool { self.s }
}

fn format_reg_list<T: std::fmt::Write>(f: &mut T, mut list: u16, colors: Option<&ColorSettings>) -> Result<(), std::fmt::Error> {
    write!(f, "{{")?;
    let mut i = 0;
    let mut tail = false;
    while i < 16 {
        let present = (list & 1) == 1;
        if present {
            if tail {
                write!(f, ", ")?;
            } else {
                tail = true;
            }
            write!(f, "{}", reg_name_colorize(i, colors))?;
        }
        i += 1;
        list >>= 1;
    }
    write!(f, "}}")
}

#[allow(non_snake_case)]
fn format_shift<T: std::fmt::Write>(f: &mut T, Rm: u8, shift: ShiftSpec, colors: Option<&ColorSettings>) -> Result<(), std::fmt::Error> {
    fn shift_tpe_to_str(tpe: u8) -> &'static str {
        match tpe {
            0b00 => "lsl",
            0b01 => "lsr",
            0b10 => "asr",
            0b11 => "ror",
            _ => { unreachable!(); }
        }
    }
    match shift {
        ShiftSpec::Immediate(0) => {
            write!(f, "{}", reg_name_colorize(Rm, colors))
        },
        ShiftSpec::Immediate(v) => {
            let tpe = v & 0x3;
            let imm = v >> 2;
            write!(f, "{}, {} {}", reg_name_colorize(Rm, colors), shift_tpe_to_str(tpe), imm)
        },
        ShiftSpec::Register(v) => {
            let tpe = v & 0x3;
            let Rs = v >> 3;
            write!(f, "{}, {} {}", reg_name_colorize(Rm, colors), shift_tpe_to_str(tpe), reg_name_colorize(Rs, colors))
        },
    }
}

#[allow(non_snake_case)]
fn format_reg_shift_mem<T: std::fmt::Write>(f: &mut T, Rd: u8, Rm: u8, shift: ShiftSpec, add: bool, pre: bool, wback: bool, colors: Option<&ColorSettings>) -> Result<(), std::fmt::Error> {
    let op = if add { "" } else { "-" };

    match (pre, wback) {
        (true, true) => {
            write!(f, "[{}, {}", reg_name_colorize(Rd, colors), op)?;
            format_shift(f, Rm, shift, colors)?;
            write!(f, "]!")
        },
        (true, false) => {
            write!(f, "[{}, {}", reg_name_colorize(Rd, colors), op)?;
            format_shift(f, Rm, shift, colors)?;
            write!(f, "]")
        },
        (false, true) => {
            unreachable!("I don't know how to render an operand with pre==false and wback==true, this seems like it should be LDRT");
        },
        (false, false) => {
            write!(f, "[{}], {}", reg_name_colorize(Rd, colors), op)?;
            format_shift(f, Rm, shift, colors)
        }
    }
}

#[allow(non_snake_case)]
fn format_reg_imm_mem<T: std::fmt::Write>(f: &mut T, Rn: u8, imm: u32, add: bool, pre: bool, wback: bool, colors: Option<&ColorSettings>) -> Result<(), std::fmt::Error> {
    if imm != 0 {
        let op = if add { "" } else { "-" };

        match (pre, wback) {
            (true, true) => {
                write!(f, "[{}, #{}{:#x}]!", reg_name_colorize(Rn, colors), op, imm * 4)
            },
            (true, false) => {
                write!(f, "[{}, #{}{:#x}]", reg_name_colorize(Rn, colors), op, imm * 4)
            },
            (false, true) => {
                unreachable!("I don't know how to render an operand with pre==false and wback==true, this seems like it should be LDRT");
            },
            (false, false) => {
                write!(f, "[{}], #{}{:#x}", reg_name_colorize(Rn, colors), op, imm * 4)
            }
        }
    } else {
        match (pre, wback) {
            (true, true) => {
                write!(f, "[{}]!", reg_name_colorize(Rn, colors))
            },
            (true, false) => {
                write!(f, "[{}]", reg_name_colorize(Rn, colors))
            },
            (false, true) => {
                unreachable!("I don't know how to render an operand with pre==false and wback==true, this seems like it should be LDRT");
            },
            (false, false) => {
                write!(f, "[{}]", reg_name_colorize(Rn, colors))
            }
        }
    }
}
fn reg_name_colorize(num: u8, colors: Option<&ColorSettings>) -> Colored<&'static str> {
    match num {
        0 => colors.register("r0"),
        1 => colors.register("r1"),
        2 => colors.register("r2"),
        3 => colors.register("r3"),
        4 => colors.register("r4"),
        5 => colors.register("r5"),
        6 => colors.register("r6"),
        7 => colors.register("r7"),
        8 => colors.register("r8"),
        9 => colors.register("sb"),
        10 => colors.register("r10"),
        11 => colors.register("fp"),
        12 => colors.register("ip"),
        13 => colors.register("sp"),
        14 => colors.register("lr"),
        15 => colors.program_counter("pc"),
        _ => { unreachable!(); }
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        self.contextualize(None, 0, None, f)
    }
}

impl LengthedInstruction for Instruction {
    type Unit = <ARMv7 as Arch>::Address;
    fn min_size() -> Self::Unit {
        4
    }
    fn len(&self) -> Self::Unit {
        4
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ConditionCode {
    EQ,
    NE,
    HS,
    LO,
    MI,
    PL,
    VS,
    VC,
    HI,
    LS,
    GE,
    LT,
    GT,
    LE,
    AL
}

impl Display for ConditionCode {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        match self {
            ConditionCode::EQ => write!(f, "eq"),
            ConditionCode::NE => write!(f, "ne"),
            ConditionCode::HS => write!(f, "hs"),
            ConditionCode::LO => write!(f, "lo"),
            ConditionCode::MI => write!(f, "mi"),
            ConditionCode::PL => write!(f, "pl"),
            ConditionCode::VS => write!(f, "vs"),
            ConditionCode::VC => write!(f, "vc"),
            ConditionCode::HI => write!(f, "hi"),
            ConditionCode::LS => write!(f, "ls"),
            ConditionCode::GE => write!(f, "ge"),
            ConditionCode::LT => write!(f, "lt"),
            ConditionCode::GT => write!(f, "gt"),
            ConditionCode::LE => write!(f, "le"),
            ConditionCode::AL => Ok(())
        }
    }
}

impl ConditionCode {
    pub fn build(value: u8) -> ConditionCode {
        match value {
            0b0000 => ConditionCode::EQ,
            0b0001 => ConditionCode::NE,
            0b0010 => ConditionCode::HS,
            0b0011 => ConditionCode::LO,
            0b0100 => ConditionCode::MI,
            0b0101 => ConditionCode::PL,
            0b0110 => ConditionCode::VS,
            0b0111 => ConditionCode::VC,
            0b1000 => ConditionCode::HI,
            0b1001 => ConditionCode::LS,
            0b1010 => ConditionCode::GE,
            0b1011 => ConditionCode::LT,
            0b1100 => ConditionCode::GT,
            0b1101 => ConditionCode::LE,
            0b1110 => ConditionCode::AL,
            _ => {
                // this means the argument `value` must never be outside [0,15]
                // which itself means this function shouldn't be public
                unreachable!();
            }
        }
    }
}

#[derive(Default, Debug)]
pub struct InstDecoder {}

#[allow(non_snake_case)]
impl Decoder<Instruction> for InstDecoder {
    fn decode<T: IntoIterator<Item=u8>>(&self, bytes: T) -> Option<Instruction> {
        let mut blank = Instruction::blank();
        match self.decode_into(&mut blank, bytes) {
            Some(_) => Some(blank),
            None => None
        }
    }
    fn decode_into<T: IntoIterator<Item=u8>>(&self, inst: &mut Instruction, bytes: T) -> Option<()> {
        fn read_word<T: IntoIterator<Item=u8>>(bytes: T) -> Option<u32> {
            let mut iter = bytes.into_iter();
            let instr: u32 =
                ((iter.next()? as u32)      ) |
                ((iter.next()? as u32) << 8 ) |
                ((iter.next()? as u32) << 16) |
                ((iter.next()? as u32) << 24);

            Some(instr)
        }

        let word = match read_word(bytes) {
            Some(word) => word,
            None => { return None; }
        };

        let (cond, opc_upper) = {
            let top_byte = word >> 24;
            (
                ((top_byte >> 4) & 0xf) as u8,
                ((top_byte >> 1) & 0x7) as u8
            )
        };

        if cond == 0b1111 {
            // do unconditional instruction stuff
            inst.condition = ConditionCode::AL;
            let op1 = (word >> 20) as u8;
            if op1 > 0x80 {
                match (op1 >> 5) & 0b11 {
                    0b00 => {
                        inst.opcode = Opcode::Incomplete(word);
                    }
                    0b01 => {
                        inst.opcode = Opcode::BLX;
                        let operand = ((word & 0xffffff) as i32) << 8 >> 6;
                        inst.operands = Operands::BranchOffset(
                            operand | (
                                ((word >> 23) & 0b10) as i32
                            )
                        );
                    }
                    0b10 => {
                        inst.opcode = Opcode::Incomplete(word);
                    }
                    0b11 => {
                        inst.opcode = Opcode::Incomplete(word);
                    }
                    _ => {
                        unreachable!();
                    }
                }
            } else {
                inst.opcode = Opcode::Incomplete(word);
            }
            return Some(());
        } else {
            inst.condition = ConditionCode::build(cond);
        }

        // distinction at this point is on page A5-192
        match opc_upper {
            0b000 => {
                // the instruction looks like
                // |c o n d|0 0 0|x x x x|x|x x x x|x x x x|x x x x x|x x|x|x x x x|
                let (s, opcode) = {
                    let part = word >> 20;
                    (
                        (part & 0x01) == 1,
                        ((part >> 1) & 0x0f) as u8
                    )
                };

                if (word & 0b10010000) == 0b10010000 {
                    // the instruction looks like
                    // |c o n d|0 0 0|x x x x|x|x x x x|x x x x|x x x x 1|x x|1|x x x x|
                    // which is a category of multiplies and extra load/store
                    if (word & 0x0f0000f0) == 0x00000090 {
                    // |c o n d|0 0 0 0|x x x x x x x x x x x x x x x x|1 0 0 1|x x x x|
                        // Multiply instruction extension space
                        // (page A5-200)
                        let op = ((word >> 20) & 0x0f) as u8;
                        let s = (op & 1) == 1;
                        let op = op >> 1;
                        let R = [
                            (word & 0x0f) as u8,
                            ((word >> 8) & 0x0f) as u8,
                            ((word >> 12) & 0x0f) as u8,
                            ((word >> 16) & 0x0f) as u8
                        ];
                        inst.set_S(s);
                        match op {
                            0b000 => {
                                inst.opcode = Opcode::MUL;
                                inst.operands = Operands::MulThreeRegs(R[3], R[0], R[1]);
                            },
                            0b001 => {
                                inst.opcode = Opcode::MLA;
                                inst.operands = Operands::MulFourRegs(R[3], R[0], R[1], R[2]);
                            },
                            0b010 => {
                                if s {
                                    inst.opcode = Opcode::Invalid;
                                    return None;
                                }
                                inst.opcode = Opcode::UMAAL;
                                inst.operands = Operands::MulFourRegs(R[2], R[3], R[0], R[1]);
                            },
                            0b011 => {
                                if s {
                                    inst.opcode = Opcode::Invalid;
                                    return None;
                                }
                                inst.opcode = Opcode::MLS;
                                inst.operands = Operands::MulFourRegs(R[3], R[0], R[1], R[2]);
                            }
                            0b100 => {
                                inst.opcode = Opcode::UMULL;
                                inst.operands = Operands::MulFourRegs(R[2], R[3], R[0], R[1]);
                            }
                            0b101 => {
                                inst.opcode = Opcode::UMLAL;
                                inst.operands = Operands::MulFourRegs(R[2], R[3], R[0], R[1]);
                            }
                            0b110 => {
                                inst.opcode = Opcode::SMULL;
                                inst.operands = Operands::MulFourRegs(R[2], R[3], R[0], R[1]);
                            }
                            0b111 => {
                                inst.opcode = Opcode::SMLAL;
                                inst.operands = Operands::MulFourRegs(R[2], R[3], R[0], R[1]);
                            }
                            _ => { unreachable!(format!("mul upcode: {:x}", op)) }
                        }
                    } else {
                    // |c o n d|0 0 0 u|x x x x x x x x x x x x x x x x|1 u u 1|x x x x|
                    // with at least one of u being 1
                    // misc instructions
                        let (flags, Rn, Rd, HiOffset, op, LoOffset) = {
                            let LoOffset = (word & 0x0f) as u8;
                            let word = word >> 5;
                            let op = (word & 0x3) as u8;
                            let word = word >> 3;
                            let HiOffset = (word & 0x0f) as u8;
                            let word = word >> 4;
                            let Rd = (word & 0x0f) as u8;
                            let word = word >> 4;
                            let Rn = (word & 0x0f) as u8;
                            let word = word >> 4;
                            let flags = (word & 0x1f) as u8;
                            (flags, Rn, Rd, HiOffset, op, LoOffset)
                        };
                        println!("{:032b}", word);
                        println!("       {:05b}|{:04b}|{:04b}|{:04b}|1{:02b}1|{:04b}", flags, Rn, Rd, HiOffset, op, LoOffset);
                        match op {
                            0b00 => {
                    // |c o n d|0 0 0 1|x x x x x x x x x x x x x x x x|1 0 0 1|x x x x|
                                // this is swp or {ld,st}ex, conditional on bit 23
                                match flags {
                                    0b10000 => {
                                        inst.opcode = Opcode::SWP;
                                        inst.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    },
                                    0b10001 | 0b10010 | 0b10011 => {
                                        inst.opcode = Opcode::Invalid;
                                        return None;
                                    }
                                    0b10100 => {
                                        inst.opcode = Opcode::SWPB;
                                        inst.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    },
                                    0b10101 | 0b10110 | 0b10111 => {
                                        inst.opcode = Opcode::Invalid;
                                        return None;
                                    }
                                    0b11000 => {
                                        inst.opcode = Opcode::STREX;
                                        inst.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    0b11001 => {
                                        inst.opcode = Opcode::LDREX;
                                        inst.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    0b11010 => {
                                        inst.opcode = Opcode::STREXD;
                                        inst.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    0b11011 => {
                                        inst.opcode = Opcode::LDREXD;
                                        inst.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    0b11100 => {
                                        inst.opcode = Opcode::STREXB;
                                        inst.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    0b11101 => {
                                        inst.opcode = Opcode::LDREXB;
                                        inst.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    0b11110 => {
                                        inst.opcode = Opcode::STREXH;
                                        inst.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    0b11111 => {
                                        inst.opcode = Opcode::LDREXH;
                                        inst.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    _ => {
                                        /*
                                         * This is unreachable because we have checked op is b1001,
                                         * meaning the high bit of flags *MUST* be 1.
                                         *
                                         * high bit and mid-bits of op all being 0 was checked
                                         * before reaching here.
                                         */
                                        unreachable!(format!("load/store flags: {:x}", flags));
                                    }
                                }
                            }
                            0b01 => {
                    // |c o n d|0 0 0 x|x x x x x x x x x x x x x x x x|1 0 1 1|x x x x|
                    // page A5-201
                                inst.opcode = Opcode::Incomplete(word);
                                // return Some(());
                                match flags {
                                    0b00010 => {
                                        // inst.opcode = Opcode::STRHT_sub;
                                        inst.opcode = Opcode::Incomplete(word);
                                        inst.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    0b01010 => {
                                        // inst.opcode = Opcode::STRHT_add;
                                        inst.opcode = Opcode::Incomplete(word);
                                        inst.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    0b00110 => {
                                        // inst.opcode = Opcode::STRHT_sub;
                                        inst.opcode = Opcode::Incomplete(word);
                                        let imm = (HiOffset << 4) as u16 | LoOffset as u16;
                                        inst.operands = Operands::ThreeOperandImm(Rn, Rd, imm);
                                    }
                                    0b01110 => {
                                        // inst.opcode = Opcode::STRHT_add;
                                        inst.opcode = Opcode::Incomplete(word);
                                        let imm = (HiOffset << 4) as u16 | LoOffset as u16;
                                        inst.operands = Operands::ThreeOperandImm(Rn, Rd, imm);
                                    }
                                    _ => {
                                        unreachable!();
                                    }
                                }
                                panic!("page a5-201");
                            }
                            0b10 => {
                    // |c o n d|0 0 0 x|x x x x x x x x x x x x x x x x|1 1 0 1|x x x x|
                    // page A5-201
                                inst.opcode = Opcode::Incomplete(word);
                                return Some(());
                            }
                            0b11 => {
                    // |c o n d|0 0 0 x|x x x x x x x x x x x x x x x x|1 1 1 1|x x x x|
                    // page A5-201
                                inst.opcode = Opcode::Incomplete(word);
                                return Some(());
                            }
                            _ => { unreachable!(); }
                        }
                    }
                } else {
                    // we know this is data processing with imm or reg shift, OR
                    // misc instructions in Figure A3-4

                    if s == false && opcode >= 0b1000 && opcode < 0b1100 {
                        let op2 = ((word >> 4) & 0x0f) as u8;
                        // the instruction looks like
                        // |c o n d|0 0 0|1 0 x x|0|x x x x|x x x x|x x x x x|x x|x|x x x x|
                        if op2 & 0x08 == 0x00 {
                            let op2 = op2 & 0x07;
                            // |c o n d|0 0 0|1 0 x x|0|x x x x|x x x x|x x x x|0|x x|x|x x x x|
                            // misc instructions (page A5-194)
                            match op2 {
                                0b000 => {
                                    
                                },
                                0b001 => {
                                    
                                },
                                0b010 => {
                                    
                                },
                                0b011 => {
                                    if opcode & 0b11 == 0b01 {
                                        inst.opcode = Opcode::BLX;
                                        inst.operands = Operands::OneOperand((word & 0x0f) as u8);
                                        return Some(());
                                    } else {
                                        return None;
                                    }
                                },
                                0b100 => {
                                    inst.opcode = Opcode::Incomplete(word);
                                    return Some(());
                                },
                                0b101 => {

                                }
                                0b110 => {
                                },
                                0b111 => {

                                },
                                _ => {
                                    unreachable!();
                                }
                            }
                        } else {
                            // |c o n d|0 0 0|1 0 x x|0|x x x x|x x x x|x x x x|1|x x|x|x x x x|
                            // multiply and multiply-accumulate 
                            inst.opcode = Opcode::Incomplete(word);
                            return Some(());
                        }
                    } else {
                        if opcode >= 16 {
                            unreachable!();
                        }
                        inst.opcode = DATA_PROCESSING_OPCODES[opcode as usize];
                        inst.set_S(s);

                        // at this point we know this is a data processing instruction
                        // either immediate shift or register shift
                        if word & 0b00010000 == 0 {
                    // |c o n d|0 0 0|1 0 x x|0|x x x x|x x x x|x x x x x|x x|0|x x x x|
                    // interpret the operands as
                    // | Rn | Rd | shift amount | shift | 0 | Rm |
                            let (Rn, Rd, shift_spec, Rm) = {
                                let Rm = (word & 0x0f) as u8;
                                let word = word >> 5;
                                let shift_spec = (word & 0x7f) as u8;
                                let word = word >> 7;
                                let Rd = (word & 0x0f) as u8;
                                let Rn = ((word >> 4) & 0x0f) as u8;
                                (Rn, Rd, shift_spec, Rm)
                            };

                            if shift_spec == 0 {
                                if (0b1101 & opcode) == 0b1101 {
                                    // MOV or MVN
                                    inst.operands = Operands::TwoOperand(Rd, Rm);
                                } else {
                                    inst.operands = Operands::ThreeOperand(Rd, Rn, Rm);
                                }
                            } else {
                                /*
                                 * TODO: look at how this interacts with mov and mvn
                                 */
                                inst.operands = Operands::ThreeOperandWithShift(Rd, Rn, Rm, ShiftSpec::Immediate(shift_spec));
                            }
                        } else {
                    //    known 0 because it and bit 5 are not both 1 --v
                    // |c o n d|0 0 0|1 0 x x|0|x x x x|x x x x|x x x x 0|x x|1|x x x x|
                            // interpret the operands as
                            // | Rn | Rd | Rs | 0 | shift | 1 | Rm |
                            let (Rn, Rd, shift_spec, Rm) = {
                                let Rm = (word & 0x0f) as u8;
                                let word = word >> 5;
                                let shift_spec = (word & 0x7f) as u8;
                                let word = word >> 7;
                                let Rd = (word & 0x0f) as u8;
                                let Rn = ((word >> 4) & 0x0f) as u8;
                                (Rn, Rd, shift_spec, Rm)
                            };
                            // page A5-200 indicates that saturating add and subtract should be
                            // here?
                            if (0b1101 & opcode) == 0b1101 {
                                // these are all invalid
                                inst.opcode = Opcode::Invalid;
                                return None;
                            } else {
                                inst.operands = Operands::ThreeOperandWithShift(Rd, Rn, Rm, ShiftSpec::Register(shift_spec));
                            }
                        }
                    }
                }
            },
            0b001 => {
                // the instruction looks like
                // |c o n d|0 0 1|x x x x|x|x x x x|x x x x|x x x x x|x x|x|x x x x|
                // bottom part of table A5-2 on page A5-194
                let (s, opcode) = {
                    let part = word >> 20;
                    (
                        (part & 0x01) == 1,
                        ((part >> 1) & 0x0f) as u8
                    )
                };
                if s == false && opcode >= 0b1000 && opcode < 0b1100 {
                // the instruction looks like
                // |c o n d|0 0 0|1 0 x x|0|x x x x|x x x x|x x x x x|x x|x|x x x x|
                // misc instructions (page A5-194)
                    inst.opcode = Opcode::Incomplete(word);
                    return Some(());
                } else {
                    if opcode >= 16 {
                        unreachable!();
                    }
                    inst.opcode = DATA_PROCESSING_OPCODES[opcode as usize];
                    inst.set_S(s);

                    let (Rn, imm) = {
                        let imm = word & 0x0000ffff;
                        let word = word >> 16;
                        ((word & 0x0f) as u8, imm)
                    };
                    if (opcode == 0b0010 || opcode == 0b0100) && Rn == 0b1111 {
                        inst.opcode = Opcode::ADR;
                    }
                    match opcode {
                        0b1101 => {
                            inst.operands = Operands::RegImm(
                                ((word >> 12) & 0xf) as u8,
                                (word & 0x0fff) as u32
                            );
                        }
                        _ => {
                            inst.operands = Operands::RegImm(Rn, imm);
                        }
                    }

                }
                /* ... */
            }
            0b010 => {
                let Rn = ((word >> 16) & 0x0f) as u8;
                let op = ((word >> 20) & 0x1f) as u8;
                let add = (op & 0b01000) != 0;
                let (imm, Rt) = {
                    ((word & 0x0fff) as u16, ((word >> 12) & 0x0f) as u8)
                };
                if (op & 0b10010) == 0b00010 {
                    let op = op & 0b00111;
                // |c o n d|0 1 0|0 x x 1 x|x x x x x x x x x x x x x x x|x|x x x x|
                    /*
                    0x010 -> STRT
                    0x011 -> LDRT
                    0x110 -> STRBT
                    0x111 -> LDRBT
                    */
                    inst.opcode = match op {
                        0b010 => Opcode::STRT(add),
                        0b011 => Opcode::LDRT(add),
                        0b110 => Opcode::STRBT(add),
                        0b111 => Opcode::LDRBT(add),
                        _ => { unreachable!(); }
                    };
                } else {
                    /*
                    xx0x0 not 0x010 -> STR (imm)
                    xx0x1 not 0x011 -> LDR (imm)
                    xx1x0 not 0x110 -> STRB (imm)
                    xx1x1 not 0x111 -> LDRB (imm)
                    */
                    let pre = (op & 0b10000) != 0;
                    let wback = (op & 0b00010) != 0;
                    let op = op & 0b00101;
                    inst.opcode = match op {
                        0b000 => Opcode::STR(add, pre, wback),
                        0b001 => {
                            if Rn == 0b1111 {
                                inst.operands = Operands::RegImm(Rt, imm.into());
                                inst.opcode = Opcode::LDR(add, pre, wback);
                                return Some(());
                            }
                            Opcode::LDR(add, pre, wback)
                        },
                        0b100 => Opcode::STRB(add, pre, wback),
                        0b101 => {
                            if Rn == 0b1111 {
                                inst.operands = Operands::RegImm(Rt, imm.into());
                                inst.opcode = Opcode::LDRB(add, pre, wback);
                                return Some(());
                            }
                            Opcode::LDRB(add, pre, wback)
                        },
                        _ => { unreachable!(); }
                    };
                }
                inst.operands = Operands::TwoRegImm(Rn, Rt, imm.into());
            },
            0b011 => {
                // page A5-192 to distinguish the following:
                // check for media instructions, and if not, load/store word and unsigned byte
                if (word & 0x00000010) != 0 {
                // |c o n d|0 1 1|x x x x|x|x x x x|x x x x|x x x x x|x x|1|x x x x|
                    // using language from A5-206: A == 1 and B == 1
                    // so this is media instructions (A5-207)
                } else {
                // |c o n d|0 1 1|x x x x|x|x x x x|x x x x|x x x x x|x x|0|x x x x|
                    // instructions here are A == 1, B == 0 in A5-206
                    let op = ((word >> 20) & 0x1f) as u8;

                    let add = (op & 0b01000) != 0;
                    /*
                        xx0x0 not 0x010 -> STR (register)
                        0x010 -> STRT
                        xx0x1 not 0x011 -> LDR (register)
                        0x011 -> LDRT
                        xx1x0 not 0x110 -> STRB (register)
                        0x110 -> STRBT
                        xx1x1 not 0x111 -> LDRB (register)
                        0x111 -> LDRBT
                    */
                    let Rn = ((word >> 16) & 0x0f) as u8;
                    if (op & 0b10010) == 0b00010 {
                        let op = op & 0b00111;
                // |c o n d|0 1 1|0 x x 1 x|x x x x x x x x x x x x x x x|0|x x x x|
                        /*
                        0x010 -> STRT
                        0x011 -> LDRT
                        0x110 -> STRBT
                        0x111 -> LDRBT
                        */
                        inst.opcode = match op {
                            0b010 => Opcode::STRT(add),
                            0b011 => Opcode::LDRT(add),
                            0b110 => Opcode::STRBT(add),
                            0b111 => Opcode::LDRBT(add),
                            _ => { unreachable!(); }
                        };
                    } else {
                        /*
                        xx0x0 not 0x010 -> STR (imm)
                        xx0x1 not 0x011 -> LDR (imm)
                        xx1x0 not 0x110 -> STRB (imm)
                        xx1x1 not 0x111 -> LDRB (imm)
                        */
                        let pre = (op & 0b10000) != 0;
                        let wback = (op & 0b00010) != 0;
                        let op = op & 0b00101;
                        inst.opcode = match op {
                            0b000 => Opcode::STR(add, pre, wback),
                            0b001 => Opcode::LDR(add, pre, wback),
                            0b100 => Opcode::STRB(add, pre, wback),
                            0b101 => Opcode::LDRB(add, pre, wback),
                            _ => { unreachable!(); }
                        };
                    }
                    let (Rt, Rm, shift) = {
                        let Rm = (word & 0xf) as u8;
                        let word = word >> 5;
                        let shift = (word & 0x7f) as u8;
                        let word = word >> 7;
                        let Rt = (word & 0xf) as u8;
                        (Rt, Rm, shift)
                    };
                    inst.operands = Operands::ThreeOperandWithShift(Rn, Rt, Rm, ShiftSpec::Immediate(shift));
                }
                return Some(());
            },
            0b100 | 0b101 => {
                // branch, branch with link, and block data transfer
                // page A5-212
                let op = (word >> 20) & 0x3f;
                if op < 0b100000 {
                    let wback = (op & 0b000010) != 0;
                    let add = (op & 0b001000) != 0;
                    let pre = (op & 0b010000) != 0;
                    let usermode = (op & 0b000100) != 0;
                    inst.opcode = if (op & 1) == 0 {
                            Opcode::STM(add, pre, wback, usermode)
                        } else {
                            Opcode::LDM(add, pre, wback, usermode)
                        };
                    inst.operands = Operands::RegRegList(
                        ((word >> 16) & 0xf) as u8,
                        (word & 0xffff) as u16
                    );
                } else if op < 0b110000 {
                    // 10xxxx
                    // the + 1 is to compensate for an architecturally-defined initial offset
                    inst.opcode = Opcode::B;
                    inst.operands = Operands::BranchOffset(((word & 0x00ffff) + 1) as i16 as i32);
                } else {
                    // 11xxxx
                    // the + 1 is to compensate for an architecturally-defined initial offset
                    inst.opcode = Opcode::BL;
                    inst.operands = Operands::BranchOffset(((word & 0x00ffff) + 1) as i16 as i32);
                }
            },
            0b110 | 0b111 => {
                // coprocessor instructions and supervisor call
                // page A5-213
                inst.opcode = Opcode::Incomplete(word);
                return Some(());
            },
            _ => { unreachable!(); }
        }
        Some(())
    }
}

#[cfg(feature="use-serde")]
#[derive(Debug, Serialize, Deserialize)]
pub struct ARMv7;

#[cfg(not(feature="use-serde"))]
#[derive(Debug)]
pub struct ARMv7;

impl Arch for ARMv7 {
    type Address = u32;
    type Instruction = Instruction;
    type Decoder = InstDecoder;
    type Operand = Operands;
}


/*
 * tests: (armv7?)
 * [0x00, 0x00, 0x90, 0xe0]
 * adds r0, r0, r0
 *
 * [0x00, 0x00, 0x82, 0xe0]
 * add r0, r2, r0
 *
 * [0x00, 0x00, 0x88, 0xe0]
 * add r0, r8, r0
 *
 * [0x00, 0x01, 0x80, 0xe0]
 * add r0, r0, r0, lsl 2
 *
 * [0x00, 0x80, 0x00, 0x00]
 * andeq r8, r0, r0
 *
 * [0xc0, 0x80, 0x20, 0x00]
 * eoreq r8, r0, r0, asr 1
 *
 * [0x00, 0x00, 0xa2, 0xe1]
 * mov r0, r0
 *
 * [0x00, 0x00, 0xaf, 0xe1]
 * mov r0, r0
 *
 * [0x10, 0x00, 0xaf, 0xe1]
 * invalid
 *
 * [0x01, 0x00, 0xaf, 0xe1]
 * mov r0, r1
 *
 * [0x00, 0x01, 0xaf, 0xe1]
 * invalid
 *
 * [0x00, 0x00, 0xa0, 0xe1]
 * mov r0, r0
 *
 * [0x00, 0x01, 0xa0, 0xe1]
 * lsl r0, r0, 2
 * # is this equivalent to mov r0, r0<<2?
 * 0180afe1 invalid
 * 018076e1 cmn r6, r1
 * 015096e1 orrs r5, r6, r1
 * 018086e1 orr r8, r6, r1
 * 0180a6e1 invalid
 * 0180d6e1 bics r8, r6, r1
 * 0180d0e1 bics r8, r0, r1
 * 8110d0e1 bics r1, r0, r1, lsl 1
 * 1200dfe1 bics r0, pc, r2, lsl r0
 * f110d0e1 ldrsh r1, [r0, 1]
 * 0101a0e1 lsl r0, r1, 2
 * 0110a0e1 mov r1, r1
 * 0111a0e1 lsl r1, r1, 2
 * 4110a0e1 asr r1, r1, 0x20
 * 2110a0e1 lsr r1, r1, 0x20
 *
 */
