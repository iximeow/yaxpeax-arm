/// Manual references in this crate, both figure and page numbers, are with respect to the document
/// `DDI0406C_d_armv7ar_arm.pdf`
/// `sha256: 294668ae6480133b32d85e9567cc77c5eb0e1232decdf42cac7ab480e884f6e0`

//#[cfg(feature="use-serde")]
//use serde::{Serialize, Deserialize};

use std::fmt::{self, Display, Formatter};

use yaxpeax_arch::{Arch, Colorize, Decoder, LengthedInstruction, NoColors, ShowContextual, YaxColors};

pub struct ConditionedOpcode(pub Opcode, pub bool, pub ConditionCode);

impl Display for ConditionedOpcode {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}", self.0, if self.1 { "s" } else { "" }, self.2)
    }
}

pub struct NoContext;

fn reg_name_colorize<C: fmt::Display, Y: YaxColors<C>>(reg: Reg, colors: &Y) -> impl fmt::Display {
    match reg.number() {
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

#[allow(non_snake_case)]
impl <T: fmt::Write, Color: fmt::Display, Y: YaxColors<Color>> ShowContextual<u32, NoContext, Color, T, Y> for Instruction {
    fn contextualize(&self, colors: &Y, _address: u32, _context: Option<&NoContext>, out: &mut T) -> fmt::Result {
        match self.opcode {
            Opcode::LDR(true, false, false) => {
                match self.operands {
                    [Operand::Reg(Rt), Operand::RegDisp(Reg { bits: 13 }, 4), Operand::Nothing, Operand::Nothing] => {
                        ConditionedOpcode(Opcode::POP, self.s, self.condition).colorize(colors, out)?;
                        return write!(out, " {{{}}}", reg_name_colorize(Rt, colors));
                    },
                    _ => {}
                }
            },
            Opcode::STR(false, true, true) => {
                match self.operands {
                    [Operand::Reg(Rt), Operand::RegDisp(Reg { bits: 13 }, 4), Operand::Nothing, Operand::Nothing] => {
                        ConditionedOpcode(Opcode::PUSH, self.s, self.condition).colorize(colors, out)?;
                        return write!(out, " {{{}}}", reg_name_colorize(Rt, colors));
                    },
                    _ => {}
                }
            },
            Opcode::LDM(true, false, true, _usermode) => {
                // TODO: what indicates usermode in the ARM syntax?
                match self.operands {
                    [Operand::Reg(Reg { bits: 13 }), Operand::RegList(list), Operand::Nothing, Operand::Nothing] => {
                        ConditionedOpcode(Opcode::POP, self.s, self.condition).colorize(colors, out)?;
                        write!(out, " ")?;
                        return format_reg_list(out, list, colors);
                    }
                    _ => {}
                }
            }
            Opcode::STM(false, true, true, _usermode) => {
                // TODO: what indicates usermode in the ARM syntax?
                match self.operands {
                    [Operand::Reg(Reg { bits: 13 }), Operand::RegList(list), Operand::Nothing, Operand::Nothing] => {
                        ConditionedOpcode(Opcode::PUSH, self.s, self.condition).colorize(colors, out)?;
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
                match &self.operands {
                    [Operand::Reg(Rn), Operand::Reg(Rt), Operand::Imm12(imm), Operand::Nothing] => {
                        ConditionedOpcode(self.opcode, self.s, self.condition).colorize(colors, out)?;
                        write!(
                            out, " {}, ",
                            reg_name_colorize(*Rt, colors),
                        )?;
                        return format_reg_imm_mem(out, *Rn, *imm, add, pre, wback, colors);
                    }
                    [Operand::Reg(Rn), Operand::RegDisp(Rt, offset), Operand::Nothing, Operand::Nothing] => {
                        ConditionedOpcode(self.opcode, self.s, self.condition).colorize(colors, out)?;
                        write!(
                            out, " {}, ",
                            reg_name_colorize(*Rn, colors),
                        )?;
                        let (add, offset) = if *offset < 0 {
                            (false, -*offset as u16)
                        } else {
                            (true, *offset as u16)
                        };
                        return format_reg_imm_mem(out, *Rt, offset, add, true, false, colors);
                    }
                    // TODO: this might not be necessary
                    [Operand::Reg(Rt), Operand::Imm12(imm), Operand::Nothing, Operand::Nothing] => {
                        ConditionedOpcode(self.opcode, self.s, self.condition).colorize(colors, out)?;
                        write!(
                            out, " {}, ",
                            reg_name_colorize(*Rt, colors)
                        )?;
                        return format_reg_imm_mem(out, Reg::from_u8(15), *imm, add, pre, wback, colors);
                    },
                    [Operand::Reg(Rd), Operand::Reg(Rn), Operand::RegShift(shift), Operand::Nothing] => {
                        ConditionedOpcode(self.opcode, self.s, self.condition).colorize(colors, out)?;
                        write!(
                            out, " {}, ",
                            reg_name_colorize(*Rn, colors)
                        )?;
                        return format_reg_shift_mem(out, *Rd, *shift, add, pre, wback, colors);
                    }
                    [Operand::Reg(Rt), Operand::RegDerefPostindexOffset(Rn, offset), Operand::Nothing, Operand::Nothing] => {
                        ConditionedOpcode(self.opcode, self.s, self.condition).colorize(colors, out)?;
                        write!(
                            out, " {}, ",
                            reg_name_colorize(*Rt, colors)
                        )?;
                        return format_reg_imm_mem(out, *Rt, *offset, true, false, true, colors);
                    }
                    o => { println!("other str/ldr operands: {:?}", o); unreachable!(); }
                }
            }
            // TODO: [add, pre, usermode]
            Opcode::STM(_add, _pre, wback, _usermode) |
            Opcode::LDM(_add, _pre, wback, _usermode) => {
                match self.operands {
                    [Operand::Reg(Rr), Operand::RegList(list), Operand::Nothing, Operand::Nothing] => {
                        ConditionedOpcode(self.opcode, self.s, self.condition).colorize(colors, out)?;
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
                ConditionedOpcode(self.opcode, self.s, self.condition).colorize(colors, out)?;
                let mut ops = self.operands.iter();
                if let Some(first_op) = ops.next() {
                    write!(out, " ")?;
                    first_op.colorize(colors, out)?;
                } else {
                    return Ok(());
                }

                for op in ops {
                    if let Operand::Nothing = op {
                        break;
                    }
                    write!(out, ", ")?;
                    op.colorize(colors, out)?;
                }

                Ok(())
            }
        }
    }
}

impl <T: fmt::Write, Color: fmt::Display, Y: YaxColors<Color>> Colorize<T, Color, Y> for ConditionedOpcode {
    fn colorize(&self, colors: &Y, out: &mut T) -> fmt::Result {
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

            Opcode::CLZ |

            Opcode::MUL |
            Opcode::MLA |
            Opcode::UMAAL |
            Opcode::MLS |
            Opcode::UMULL |
            Opcode::UMLAL |
            Opcode::SMULL |
            Opcode::SMUL(_, _) |
            Opcode::SMAL(_, _) |
            Opcode::SMLA(_, _) |
            Opcode::SMLAW(_) |
            Opcode::SMLAL |
            Opcode::SMLAL_halfword(_, _) => { write!(out, "{}", colors.arithmetic_op(self)) },

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
            Opcode::MSR |
            Opcode::MRS |
            Opcode::MOV |
            Opcode::MVN => { write!(out, "{}", colors.data_op(self)) },
        }
    }
}

impl Display for Opcode {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
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
            Opcode::CLZ => { write!(f, "clz") },
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
            Opcode::MSR => { write!(f, "msr") },
            Opcode::MRS => { write!(f, "mrs") },
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
            Opcode::SMLA(first, second) => {
                write!(f, "smla{}{}", if *first { "t" } else { "b" }, if *second { "t" } else { "b" })
            }
            Opcode::SMLAL => { write!(f, "smlal") },
            Opcode::SMLAL_halfword(first, second) => {
                write!(f, "smlal{}{}", if *first { "t" } else { "b" }, if *second { "t" } else { "b" })
            }
            Opcode::SMUL(first, second) => {
                write!(f, "smul{}{}", if *first { "t" } else { "b" }, if *second { "t" } else { "b" })
            },
            Opcode::SMAL(first, second) => {
                write!(f, "smal{}{}", if *first { "t" } else { "b" }, if *second { "t" } else { "b" })
            },
            Opcode::SMLAW(second) => {
                write!(f, "smlaw{}", if *second { "t" } else { "b" })
            },
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
    MSR,
    MRS,
    CLZ,
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
    SMUL(bool, bool),
    SMLA(bool, bool),
    SMLAL,
    SMLAL_halfword(bool, bool),
    SMAL(bool, bool),
    SMLAW(bool),
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
#[repr(transparent)]
pub struct RegShift {
    data: u16
}

impl RegShift {
    fn into_shift(&self) -> RegShiftStyle {
        if self.data & 0b1000 == 0 {
            RegShiftStyle::RegImm(RegImmShift { data: self.data })
        } else {
            RegShiftStyle::RegReg(RegRegShift { data: self.data })
        }
    }

    fn from(data: u16) -> Self {
        RegShift { data }
    }
}

pub enum RegShiftStyle {
    RegImm(RegImmShift),
    RegReg(RegRegShift),
}

#[repr(transparent)]
pub struct RegRegShift {
    data: u16
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum ShiftStyle {
    LSL = 0,
    LSR = 1,
    ASR = 2,
    ROR = 3,
}

impl ShiftStyle {
    fn from(bits: u8) -> ShiftStyle {
        match bits {
            0b00 => ShiftStyle::LSL,
            0b01 => ShiftStyle::LSR,
            0b10 => ShiftStyle::ASR,
            0b11 => ShiftStyle::ROR,
            _ => unreachable!("bad ShiftStyle index")
        }
    }
}

impl RegRegShift {
    pub fn shifter(&self) -> Reg {
        Reg::from_u8((self.data >> 8) as u8 & 0b1111)
    }
    pub fn stype(&self) -> ShiftStyle {
        ShiftStyle::from((self.data >> 5) as u8 & 0b11)
    }
    pub fn shiftee(&self) -> Reg {
        Reg::from_u8(self.data as u8 & 0b1111)
    }
}

#[repr(transparent)]
pub struct RegImmShift {
    data: u16
}

impl RegImmShift {
    pub fn imm(&self) -> u8 {
        (self.data >> 7) as u8 & 0b11111
    }
    pub fn stype(&self) -> ShiftStyle {
        ShiftStyle::from((self.data >> 5) as u8 & 0b11)
    }
    pub fn shiftee(&self) -> Reg {
        Reg::from_u8(self.data as u8 & 0b1111)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct Reg {
    bits: u8
}

impl Reg {
    pub fn from_u8(bits: u8) -> Reg {
        if bits > 0b1111 {
            panic!("register number out of range");
        }

        Reg { bits }
    }

    pub fn number(&self) -> u8 {
        self.bits
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operand {
    Reg(Reg),
    RegList(u16),
    RegDeref(Reg),
    RegDisp(Reg, i16),
    RegShift(RegShift),
    RegDerefRegShift(RegShift),
    RegDerefPostindexOffset(Reg, u16),
    RegDerefPostindexReg(Reg, Reg),
    Imm12(u16),
    Imm32(u32),
    BranchOffset(i32),
    ASPR,
    CSPR,
    SPSR,
    Nothing,
}

impl <T: fmt::Write, Color: fmt::Display, Y: YaxColors<Color>> Colorize<T, Color, Y> for Operand {
    fn colorize(&self, colors: &Y, f: &mut T) -> fmt::Result {
        match self {
            Operand::RegList(list) => {
                format_reg_list(f, *list, colors)
            }
            Operand::Reg(reg) => {
                write!(f, "{}", reg_name_colorize(*reg, colors))
            }
            Operand::RegDeref(reg) => {
                write!(f, "[{}]", reg_name_colorize(*reg, colors))
            }
            Operand::RegDisp(reg, imm) => {
                write!(f, "[{} + {:#x}]", reg_name_colorize(*reg, colors), imm)
            }
            Operand::RegShift(shift) => {
                format_shift(f, *shift, colors)
            }
            Operand::RegDerefRegShift(shift) => {
                write!(f, "[")?;
                format_shift(f, *shift, colors)?;
                write!(f, "]")
            }
            Operand::RegDerefPostindexOffset(reg, offs) => {
                write!(f, "[{}, {:#x}]", reg_name_colorize(*reg, colors), offs)
            }
            Operand::RegDerefPostindexReg(reg, offsreg) => {
                write!(f, "[{}, {}]", reg_name_colorize(*reg, colors), reg_name_colorize(*offsreg, colors))
            }
            Operand::Imm12(imm) => {
                write!(f, "{:#x}", imm)
            }
            Operand::Imm32(imm) => {
                write!(f, "{:#x}", imm)
            }
            Operand::BranchOffset(imm) => {
                if *imm < 0 {
                    write!(f, " $-{:#x}", (-*imm) * 4)
                } else {
                    write!(f, " $+{:#x}", *imm * 4)
                }
            }
            Operand::ASPR => { write!(f, "aspr") },
            Operand::CSPR => { write!(f, "cspr") },
            Operand::SPSR => { write!(f, "spsr") },
            Operand::Nothing => { panic!("tried to print Nothing operand") },
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Instruction {
    pub condition: ConditionCode,
    pub opcode: Opcode,
    pub operands: [Operand; 4],
    pub s: bool
}

#[derive(Debug, PartialEq)]
pub enum DecodeError {
    ExhaustedInput,
    InvalidOpcode,
    InvalidOperand,
    Incomplete,
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f:  &mut fmt::Formatter) -> fmt::Result {
        match self {
            DecodeError::ExhaustedInput => write!(f, "exhausted input"),
            DecodeError::InvalidOpcode => write!(f, "invalid opcode"),
            DecodeError::InvalidOperand => write!(f, "invalid operand"),
            DecodeError::Incomplete => write!(f, "incomplete decoder"),
        }
    }
}

impl yaxpeax_arch::DecodeError for DecodeError {
    fn data_exhausted(&self) -> bool { self == &DecodeError::ExhaustedInput }
    fn bad_opcode(&self) -> bool { self == &DecodeError::InvalidOpcode }
    fn bad_operand(&self) -> bool { self == &DecodeError::InvalidOperand }
}

impl yaxpeax_arch::Instruction for Instruction {
    // TODO: this is wrong!!
    fn well_defined(&self) -> bool { true }
}

impl Default for Instruction {
    fn default() -> Self {
        Instruction {
            condition: ConditionCode::AL,
            opcode: Opcode::Invalid,
            operands: [Operand::Nothing, Operand::Nothing, Operand::Nothing, Operand::Nothing],
            s: false
        }
    }
}

impl Instruction {
    fn set_s(&mut self, value: bool) {
        self.s = value;
    }
    pub fn s(&self) -> bool { self.s }
}

fn format_reg_list<T: fmt::Write, C: fmt::Display, Y: YaxColors<C>>(f: &mut T, mut list: u16, colors: &Y) -> Result<(), fmt::Error> {
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
            write!(f, "{}", reg_name_colorize(Reg::from_u8(i), colors))?;
        }
        i += 1;
        list >>= 1;
    }
    write!(f, "}}")
}

#[allow(non_snake_case)]
fn format_shift<T: fmt::Write, C: fmt::Display, Y: YaxColors<C>>(f: &mut T, shift: RegShift, colors: &Y) -> Result<(), fmt::Error> {
    fn shift_tpe_to_str(tpe: ShiftStyle) -> &'static str {
        match tpe {
            ShiftStyle::LSL => "lsl",
            ShiftStyle::LSR => "lsr",
            ShiftStyle::ASR => "asr",
            ShiftStyle::ROR => "ror",
        }
    }
    match shift.into_shift() {
        RegShiftStyle::RegImm(imm_shift) => {
            if imm_shift.imm() == 0 && imm_shift.stype() == ShiftStyle::LSL {
                write!(f, "{}", reg_name_colorize(imm_shift.shiftee(), colors))
            } else {
                write!(f, "{}, {} {}", reg_name_colorize(imm_shift.shiftee(), colors), shift_tpe_to_str(imm_shift.stype()), imm_shift.imm())
            }
        }
        RegShiftStyle::RegReg(reg_shift) => {
            write!(f, "{}, {} {}", reg_name_colorize(reg_shift.shiftee(), colors), shift_tpe_to_str(reg_shift.stype()), reg_name_colorize(reg_shift.shifter(), colors))
        },
    }
}

#[allow(non_snake_case)]
fn format_reg_shift_mem<T: fmt::Write, C: fmt::Display, Y: YaxColors<C>>(f: &mut T, Rd: Reg, shift: RegShift, add: bool, pre: bool, wback: bool, colors: &Y) -> Result<(), fmt::Error> {
    let op = if add { "" } else { "-" };

    match (pre, wback) {
        (true, true) => {
            write!(f, "[{}, {}", reg_name_colorize(Rd, colors), op)?;
            format_shift(f, shift, colors)?;
            write!(f, "]!")
        },
        (true, false) => {
            write!(f, "[{}, {}", reg_name_colorize(Rd, colors), op)?;
            format_shift(f, shift, colors)?;
            write!(f, "]")
        },
        (false, true) => {
            unreachable!("I don't know how to render an operand with pre==false and wback==true, this seems like it should be LDRT");
        },
        (false, false) => {
            write!(f, "[{}], {}", reg_name_colorize(Rd, colors), op)?;
            format_shift(f, shift, colors)
        }
    }
}

#[allow(non_snake_case)]
fn format_reg_imm_mem<T: fmt::Write, C: fmt::Display, Y: YaxColors<C>>(f: &mut T, Rn: Reg, imm: u16, add: bool, pre: bool, wback: bool, colors: &Y) -> Result<(), fmt::Error> {
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

impl Display for Instruction {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        self.contextualize(&NoColors, 0, Some(&NoContext), f)
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
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
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
pub struct InstDecoder {
    system_mode: bool
}

#[allow(non_snake_case)]
impl Decoder<Instruction> for InstDecoder {
    type Error = DecodeError;

    fn decode_into<T: IntoIterator<Item=u8>>(&self, inst: &mut Instruction, bytes: T) -> Result<(), Self::Error> {
        fn read_word<T: IntoIterator<Item=u8>>(bytes: T) -> Result<u32, DecodeError> {
            let mut iter = bytes.into_iter();
            let instr: u32 =
                ((iter.next().ok_or(DecodeError::ExhaustedInput)? as u32)      ) |
                ((iter.next().ok_or(DecodeError::ExhaustedInput)? as u32) << 8 ) |
                ((iter.next().ok_or(DecodeError::ExhaustedInput)? as u32) << 16) |
                ((iter.next().ok_or(DecodeError::ExhaustedInput)? as u32) << 24);

            Ok(instr)
        }

        let word = read_word(bytes)?;

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
                        inst.operands = [
                            Operand::BranchOffset(
                                operand | (
                                    ((word >> 23) & 0b10) as i32
                                )
                            ),
                            Operand::Nothing,
                            Operand::Nothing,
                            Operand::Nothing,
                        ];
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
            return Ok(());
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
                        inst.set_s(s);
                        match op {
                            0b000 => {
                                inst.opcode = Opcode::MUL;
                                inst.operands = [
                                    Operand::Reg(Reg::from_u8(R[3])),
                                    Operand::Reg(Reg::from_u8(R[0])),
                                    Operand::Reg(Reg::from_u8(R[1])),
                                    Operand::Nothing,
                                ];
                            },
                            0b001 => {
                                inst.opcode = Opcode::MLA;
                                inst.operands = [
                                    Operand::Reg(Reg::from_u8(R[3])),
                                    Operand::Reg(Reg::from_u8(R[0])),
                                    Operand::Reg(Reg::from_u8(R[1])),
                                    Operand::Reg(Reg::from_u8(R[2])),
                                ];
                            },
                            0b010 => {
                                if s {
                                    inst.opcode = Opcode::Invalid;
                                    return Err(DecodeError::InvalidOpcode);
                                }
                                inst.opcode = Opcode::UMAAL;
                                inst.operands = [
                                    Operand::Reg(Reg::from_u8(R[2])),
                                    Operand::Reg(Reg::from_u8(R[3])),
                                    Operand::Reg(Reg::from_u8(R[0])),
                                    Operand::Reg(Reg::from_u8(R[1])),
                                ];
                            },
                            0b011 => {
                                if s {
                                    inst.opcode = Opcode::Invalid;
                                    return Err(DecodeError::InvalidOpcode);
                                }
                                inst.opcode = Opcode::MLS;
                                inst.operands = [
                                    Operand::Reg(Reg::from_u8(R[3])),
                                    Operand::Reg(Reg::from_u8(R[0])),
                                    Operand::Reg(Reg::from_u8(R[1])),
                                    Operand::Reg(Reg::from_u8(R[2])),
                                ];
                            }
                            0b100 => {
                                inst.opcode = Opcode::UMULL;
                                inst.operands = [
                                    Operand::Reg(Reg::from_u8(R[2])),
                                    Operand::Reg(Reg::from_u8(R[3])),
                                    Operand::Reg(Reg::from_u8(R[0])),
                                    Operand::Reg(Reg::from_u8(R[1])),
                                ];
                            }
                            0b101 => {
                                inst.opcode = Opcode::UMLAL;
                                inst.operands = [
                                    Operand::Reg(Reg::from_u8(R[2])),
                                    Operand::Reg(Reg::from_u8(R[3])),
                                    Operand::Reg(Reg::from_u8(R[0])),
                                    Operand::Reg(Reg::from_u8(R[1])),
                                ];
                            }
                            0b110 => {
                                inst.opcode = Opcode::SMULL;
                                inst.operands = [
                                    Operand::Reg(Reg::from_u8(R[2])),
                                    Operand::Reg(Reg::from_u8(R[3])),
                                    Operand::Reg(Reg::from_u8(R[0])),
                                    Operand::Reg(Reg::from_u8(R[1])),
                                ];
                            }
                            0b111 => {
                                inst.opcode = Opcode::SMLAL;
                                inst.operands = [
                                    Operand::Reg(Reg::from_u8(R[2])),
                                    Operand::Reg(Reg::from_u8(R[3])),
                                    Operand::Reg(Reg::from_u8(R[0])),
                                    Operand::Reg(Reg::from_u8(R[1])),
                                ];
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
                        match op {
                            0b00 => {
                    // |c o n d|0 0 0 1|x x x x x x x x x x x x x x x x|1 0 0 1|x x x x|
                                // this is swp or {ld,st}ex, conditional on bit 23
                                // see page A5-203
                                match flags {
                                    0b10000 => {
                                        inst.opcode = Opcode::SWP;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rd)),
                                            Operand::Reg(Reg::from_u8(LoOffset)),
                                            Operand::RegDeref(Reg::from_u8(Rn)),
                                            Operand::Nothing,
                                        ];
                                    },
                                    0b10001 | 0b10010 | 0b10011 => {
                                        inst.opcode = Opcode::Invalid;
                                        return Err(DecodeError::InvalidOpcode);
                                    }
                                    0b10100 => {
                                        inst.opcode = Opcode::SWPB;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rd)),
                                            Operand::Reg(Reg::from_u8(LoOffset)),
                                            Operand::RegDeref(Reg::from_u8(Rn)),
                                            Operand::Nothing,
                                        ];
                                    },
                                    0b10101 | 0b10110 | 0b10111 => {
                                        inst.opcode = Opcode::Invalid;
                                        return Err(DecodeError::InvalidOpcode);
                                    }
                                    0b11000 => {
                                        // TODO: flag v6
                                        inst.opcode = Opcode::STREX;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rd)),
                                            Operand::Reg(Reg::from_u8(LoOffset)),
                                            Operand::RegDeref(Reg::from_u8(Rn)),
                                            Operand::Nothing,
                                        ];
                                    }
                                    0b11001 => {
                                        // TODO: flag v6
                                        inst.opcode = Opcode::LDREX;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rd)),
                                            Operand::RegDeref(Reg::from_u8(Rn)),
                                            Operand::Nothing,
                                            Operand::Nothing,
                                        ];
                                    }
                                    0b11010 => {
                                        inst.opcode = Opcode::STREXD;
                                        if LoOffset == 0b1110 || (LoOffset & 1 == 1) || Rd == 15 || Rn == 15 {
                                            // TODO: "unpredictable"
                                            return Err(DecodeError::InvalidOperand);
                                        }
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rd)),
                                            Operand::Reg(Reg::from_u8(LoOffset)),
                                            Operand::Reg(Reg::from_u8(LoOffset + 1)),
                                            Operand::RegDeref(Reg::from_u8(Rn)),
                                        ];
                                    }
                                    0b11011 => {
                                        inst.opcode = Opcode::LDREXD;
                                        if LoOffset == 0b1110 || (LoOffset & 1 == 1) || Rn == 15 {
                                            // TODO: "unpredictable"
                                            return Err(DecodeError::InvalidOperand);
                                        }
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(LoOffset)),
                                            Operand::Reg(Reg::from_u8(LoOffset + 1)),
                                            Operand::RegDeref(Reg::from_u8(Rn)),
                                            Operand::Nothing,
                                        ];
                                    }
                                    0b11100 => {
                                        inst.opcode = Opcode::STREXB;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rd)),
                                            Operand::Reg(Reg::from_u8(LoOffset)),
                                            Operand::RegDeref(Reg::from_u8(Rn)),
                                            Operand::Nothing,
                                        ];
                                    }
                                    0b11101 => {
                                        inst.opcode = Opcode::LDREXB;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(LoOffset)),
                                            Operand::RegDeref(Reg::from_u8(Rn)),
                                            Operand::Nothing,
                                            Operand::Nothing,
                                        ];
                                    }
                                    0b11110 => {
                                        inst.opcode = Opcode::STREXH;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rd)),
                                            Operand::Reg(Reg::from_u8(LoOffset)),
                                            Operand::RegDeref(Reg::from_u8(Rn)),
                                            Operand::Nothing,
                                        ];
                                    }
                                    0b11111 => {
                                        inst.opcode = Opcode::LDREXH;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(LoOffset)),
                                            Operand::RegDeref(Reg::from_u8(Rn)),
                                            Operand::Nothing,
                                            Operand::Nothing,
                                        ];
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
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rd)),
                                            Operand::RegDerefPostindexReg(Reg::from_u8(Rd), Reg::from_u8(LoOffset)),
                                            Operand::Nothing,
                                            Operand::Nothing,
                                        ];
                                    }
                                    0b01010 => {
                                        // inst.opcode = Opcode::STRHT_add;
                                        inst.opcode = Opcode::Incomplete(word);
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rd)),
                                            Operand::RegDerefPostindexReg(Reg::from_u8(Rd), Reg::from_u8(LoOffset)),
                                            Operand::Nothing,
                                            Operand::Nothing,
                                        ];
                                    }
                                    0b00110 => {
                                        // inst.opcode = Opcode::STRHT_sub;
                                        inst.opcode = Opcode::Incomplete(word);
                                        let imm = (HiOffset << 4) as u16 | LoOffset as u16;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rd)),
                                            Operand::RegDerefPostindexOffset(Reg::from_u8(Rd), imm),
                                            Operand::Nothing,
                                            Operand::Nothing,
                                        ];
                                    }
                                    0b01110 => {
                                        // inst.opcode = Opcode::STRHT_add;
                                        inst.opcode = Opcode::Incomplete(word);
                                        let imm = (HiOffset << 4) as u16 | LoOffset as u16;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rd)),
                                            Operand::RegDerefPostindexOffset(Reg::from_u8(Rd), imm),
                                            Operand::Nothing,
                                            Operand::Nothing,
                                        ];
                                    }
                                    _ => {
                                        return Err(DecodeError::Incomplete);
//                                        unreachable!();
                                    }
                                }
                                return Err(DecodeError::Incomplete);
//                                panic!("page a5-201");
                            }
                            0b10 => {
                    // |c o n d|0 0 0 x|x x x x x x x x x x x x x x x x|1 1 0 1|x x x x|
                    // page A5-201
                                inst.opcode = Opcode::Incomplete(word);
                                return Ok(());
                            }
                            0b11 => {
                    // |c o n d|0 0 0 x|x x x x x x x x x x x x x x x x|1 1 1 1|x x x x|
                    // page A5-201
                                inst.opcode = Opcode::Incomplete(word);
                                return Ok(());
                            }
                            _ => { unreachable!(); }
                        }
                    }
                } else {
                    // we know this is data processing with imm or reg shift, OR
                    // misc instructions in Figure A5-4

                    if s == false && opcode >= 0b1000 && opcode < 0b1100 {
                        // Data-processing and miscellaneous instructions on page A5-194
                        let op2 = ((word >> 4) & 0x0f) as u8;
                        // the instruction looks like
                        // |c o n d|0 0 0|1 0 x x|0|x x x x|x x x x|x x x x x|x x|x|x x x x|
                        if op2 & 0x08 == 0x00 {
                            let op2 = op2 & 0x07;
                            // |c o n d|0 0 0|1 0 x x|0|x x x x|x x x x|x x x x|0|x x|x|x x x x|
                            // misc instructions (page A5-194)
                            match op2 {
                                0b000 => {
                                    if word & 0b1000000000 != 0 {
                                        // TODO: ARMv7VE flag
                                        let _M = (((word >> 9) & 1) << 4) | ((word >> 16) & 0x0f);
                                        let _R = (word >> 22) & 1;

                                        if opcode & 0b01 == 0b01 {
                                            inst.opcode = Opcode::MSR;
                                            inst.operands[1] = Operand::Reg(Reg::from_u8(word as u8 & 0b1111));
                                            return Err(DecodeError::Incomplete);
                                        } else {
                                            inst.opcode = Opcode::MRS;
                                            inst.operands[0] = Operand::Reg(Reg::from_u8((word >> 12) as u8 & 0b1111));
                                            return Err(DecodeError::Incomplete);
                                        }
                                    } else {
                                        match opcode & 0b11 {
                                            0b00 |
                                            0b10 => {
                                                inst.opcode = Opcode::MRS;
                                                /*
                                                let src = if self.system_mode {
                                                    let R = (word >> 22) & 1 != 0;
                                                    if R {
                                                        Operand::SPSR
                                                    } else {
                                                        Operand::CSPR
                                                    }
                                                } else {
                                                    Operand::ASPR
                                                };
                                                */
                                                inst.operands[0] = Operand::Reg(Reg::from_u8((word >> 12) as u8 & 0b1111));
                                                // TODO:
                                                return Err(DecodeError::Incomplete);
                                            }
                                            0b01 => {
                                                inst.opcode = Opcode::MSR;
                                                let mask = (word >> 16) & 0b1111;
                                                if self.system_mode {
                                                    let R = (word >> 22) & 1 != 0;
                                                    let _dest = if R {
                                                        Operand::SPSR
                                                    } else {
                                                        Operand::CSPR
                                                    };
                                                    // inst.operands[0] = /* masked write to dest */
                                                    inst.operands[1] = Operand::Reg(Reg::from_u8(word as u8 & 0b1111));
                                                    // TODO:
                                                    return Err(DecodeError::Incomplete);
                                                } else {
                                                    if mask & 0b11 == 0 {
                                                        inst.operands[1] = Operand::Reg(Reg::from_u8(word as u8 & 0b1111));
                                                        // TODO:
                                                        // inst.operands[0] = /* derived from mask >> 2 */
                                                        return Err(DecodeError::Incomplete);
                                                    } else {
                                                        // MSR with op == 01, op != xx00
                                                        return Err(DecodeError::InvalidOperand);
                                                    }
                                                }
                                            },
                                            0b11 => {
                                                if !self.system_mode {
                                                    return Err(DecodeError::InvalidOperand);
                                                }

                                                inst.opcode = Opcode::MSR;
                                                inst.operands[0] = Operand::Reg(Reg::from_u8((word >> 12) as u8 & 0b1111));
                                                // TODO:
                                                return Err(DecodeError::Incomplete);
                                            }
                                            _ => {
                                                unreachable!();
                                            }
                                        }
                                    }
                                },
                                0b001 => {
                                    match opcode & 0b11 {
                                        0b01 => {
                                            inst.opcode = Opcode::BX;
                                            inst.operands = [
                                                Operand::Reg(Reg::from_u8(word as u8 & 0b1111)),
                                                Operand::Nothing,
                                                Operand::Nothing,
                                                Operand::Nothing,
                                            ];
                                        }
                                        0b11 => {
                                            inst.opcode = Opcode::CLZ;
                                            inst.operands = [
                                                Operand::Reg(Reg::from_u8((word >> 12) as u8 & 0b1111)),
                                                Operand::Reg(Reg::from_u8(word as u8 & 0b1111)),
                                                Operand::Nothing,
                                                Operand::Nothing,
                                            ];
                                        }
                                        _ => {
                                            return Err(DecodeError::InvalidOpcode);
                                        }
                                    }
                                },
                                0b010 => {
                                    return Err(DecodeError::InvalidOpcode);
                                },
                                0b011 => {
                                    if opcode & 0b11 == 0b01 {
                                        inst.opcode = Opcode::BLX;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(word as u8 & 0x0f)),
                                            Operand::Nothing,
                                            Operand::Nothing,
                                            Operand::Nothing,
                                        ];
                                        return Ok(());
                                    } else {
                                        return Err(DecodeError::InvalidOpcode);
                                    }
                                },
                                0b100 => {
                                    // no row for op2 == 0b100 in table A5-14 (page A5-203)
                                    return Err(DecodeError::InvalidOpcode);
                                },
                                0b101 => {
                                    // TODO: "Saturating addition and subtraction" page A5-200
                                    return Err(DecodeError::Incomplete);
                                }
                                0b110 => {
                                    // TODO: "ERET" page B9-1968
                                    return Err(DecodeError::Incomplete);
                                },
                                0b111 => {
                                    // TODO: "BKPT, HVC, SMC" from table A5-14/page A5-203
                                    return Err(DecodeError::Incomplete);
                                },
                                _ => {
                                    unreachable!();
                                }
                            }
                        } else {
                            // |c o n d|0 0 0|1 0 x x|0|x x x x|x x x x|x x x x|1|x x|x|x x x x|
                            // Halfword multiply and multiply accumulate on page A5-200
                            match (word >> 21) & 0b11 {
                                0b00 => {
                                    let Rn_b = ((word >> 6) & 1) == 0;
                                    let Rm_b = ((word >> 5) & 1) == 0;
                                    inst.opcode = Opcode::SMLA(Rn_b, Rm_b);
                                    inst.operands = [
                                        Operand::Reg(Reg::from_u8((word >> 16) as u8 & 0b1111)),
                                        Operand::Reg(Reg::from_u8(word as u8 & 0b1111)),
                                        Operand::Reg(Reg::from_u8((word >> 8) as u8 & 0b1111)),
                                        Operand::Reg(Reg::from_u8((word >> 12) as u8 & 0b1111)),
                                    ];
                                    return Ok(());
                                },
                                0b01 => {
                                    if word & 0b10000 == 0 {
                                        // SMLAWB, SMLAWT page A8-631
                                        let Rm_b = ((word >> 5) & 1) == 0;
                                        inst.opcode = Opcode::SMLAW(Rm_b);
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8((word >> 16) as u8 & 0b1111)),
                                            Operand::Reg(Reg::from_u8(word as u8 & 0b1111)),
                                            Operand::Reg(Reg::from_u8((word >> 8) as u8 & 0b1111)),
                                            Operand::Reg(Reg::from_u8((word >> 12) as u8 & 0b1111)),
                                        ];
                                        return Ok(());
                                    } else {
                                        // SMULWB, SMULWT page A8-649
                                        let Rm_b = ((word >> 5) & 1) == 0;
                                        inst.opcode = Opcode::SMLAW(Rm_b);
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8((word >> 16) as u8 & 0b1111)),
                                            Operand::Reg(Reg::from_u8(word as u8 & 0b1111)),
                                            Operand::Reg(Reg::from_u8((word >> 8) as u8 & 0b1111)),
                                            Operand::Nothing,
                                        ];
                                        return Ok(());
                                    }
                                }
                                0b10 => {
                                    let Rn_b = ((word >> 6) & 1) == 0;
                                    let Rm_b = ((word >> 5) & 1) == 0;
                                    inst.opcode = Opcode::SMLAL_halfword(Rn_b, Rm_b);
                                    inst.operands = [
                                        Operand::Reg(Reg::from_u8((word >> 12) as u8 & 0b1111)),
                                        Operand::Reg(Reg::from_u8((word >> 16) as u8 & 0b1111)),
                                        Operand::Reg(Reg::from_u8(word as u8 & 0b1111)),
                                        Operand::Reg(Reg::from_u8((word >> 8) as u8 & 0b1111)),
                                    ];
                                    if inst.operands[0] == inst.operands[1] {
                                        // TODO: this is actually "UNPREDICTABLE" (A8-627)
                                        return Err(DecodeError::InvalidOperand);
                                    }
                                    return Ok(());
                                }
                                0b11 => {
                                    let Rn_b = ((word >> 6) & 1) == 0;
                                    let Rm_b = ((word >> 5) & 1) == 0;
                                    inst.opcode = Opcode::SMUL(Rn_b, Rm_b);
                                    inst.operands = [
                                        Operand::Reg(Reg::from_u8((word >> 16) as u8 & 0b1111)),
                                        Operand::Reg(Reg::from_u8(word as u8 & 0b1111)),
                                        Operand::Reg(Reg::from_u8((word >> 8) as u8 & 0b1111)),
                                        Operand::Nothing,
                                    ];
                                    if inst.operands[0] == inst.operands[1] {
                                        // TODO: this is actually "UNPREDICTABLE" (A8-627)
                                        return Err(DecodeError::InvalidOperand);
                                    }
                                    return Ok(());
                                }
                                _ => {
                                    unreachable!();
                                }
                            }
                        }
                    } else {
                        // `Table A5-3 Data-processing (register) instructions`, not op=10xx0.
                        if opcode >= 16 {
                            unreachable!();
                        }
                        inst.opcode = DATA_PROCESSING_OPCODES[opcode as usize];
                        inst.set_s(s);

                        // at this point we know this is a data processing instruction
                        // either immediate shift or register shift
                        if word & 0b00010000 == 0 {
                    // |c o n d|0 0 0|x x x x|0|x x x x|x x x x|x x x x x|x x|0|x x x x|
                    // interpret the operands as
                    // | Rn | Rd | shift amount | shift | 0 | Rm |
                            let (Rn, Rd, shift_spec, Rm) = {
                                let Rm = (word & 0x0f) as u8;
                                let shift_spec = (word & 0xfff) as u16;
                                let word = word >> 12;
                                let Rd = (word & 0x0f) as u8;
                                let Rn = ((word >> 4) & 0x0f) as u8;
                                (Rn, Rd, shift_spec, Rm)
                            };

                            if shift_spec & 0xff0 == 0 {
                                if (0b1101 & opcode) == 0b1101 {
                                    if Rn != 0 {
                                        // this is really a "should be zero" situation
                                        return Err(DecodeError::Incomplete);
                                    }
                                    // MOV or MVN
                                    inst.operands = [
                                        Operand::Reg(Reg::from_u8(Rd)),
                                        Operand::Reg(Reg::from_u8(Rm)),
                                        Operand::Nothing,
                                        Operand::Nothing
                                    ];
                                } else {
                                    inst.operands = [
                                        Operand::Reg(Reg::from_u8(Rd)),
                                        Operand::Reg(Reg::from_u8(Rn)),
                                        Operand::Reg(Reg::from_u8(Rm)),
                                        Operand::Nothing
                                    ];
                                }
                            } else {
                                if opcode == 0b1101 && Rn != 0 {
                                    // Rn "should" be zero
                                    return Err(DecodeError::Incomplete);
                                }

                                inst.operands = [
                                    Operand::Reg(Reg::from_u8(Rd)),
                                    Operand::Reg(Reg::from_u8(Rn)),
                                    Operand::RegShift(RegShift::from(shift_spec)),
                                    Operand::Nothing
                                ];
                            }
                        } else {
                    //    known 0 because it and bit 5 are not both 1 --v
                    // |c o n d|0 0 0|1 0 x x|0|x x x x|x x x x|x x x x 0|x x|1|x x x x|
                            // interpret the operands as
                            // | Rn | Rd | Rs | 0 | shift | 1 | Rm |
                            let (Rn, Rd, shift_spec) = {
                                let shift_spec = (word & 0xfff) as u16;
                                let word = word >> 12;
                                let Rd = (word & 0x0f) as u8;
                                let Rn = ((word >> 4) & 0x0f) as u8;
                                (Rn, Rd, shift_spec)
                            };
                            // page A5-200 indicates that saturating add and subtract should be
                            // here?
                            if (0b1101 & opcode) == 0b1101 {
                                // these are all invalid
                                inst.opcode = Opcode::Invalid;
                                return Err(DecodeError::InvalidOpcode);
                            } else {
                                // TODO: unsure about this RegShift...
                                inst.operands = [
                                    Operand::Reg(Reg::from_u8(Rd)),
                                    Operand::Reg(Reg::from_u8(Rn)),
                                    Operand::RegShift(RegShift::from(shift_spec)),
                                    Operand::Nothing,
                                ];
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
                // |c o n d|0 0 1|1 0 x x|0|x x x x|x x x x|x x x x x|x x|x|x x x x|
                // which means 16-bit immediate load, high half immediate load, or MSR (immediate)
                // + hints.
                // See table A5-2, page A5-194.
                    inst.opcode = Opcode::Incomplete(word);
                    return Ok(());
                } else {
                    // Data-processing (immediate)
                    // Page A5-197
                    if opcode >= 16 {
                        unreachable!();
                    }
                    inst.opcode = DATA_PROCESSING_OPCODES[opcode as usize];
                    inst.set_s(s);

                    let (Rn, Rd, imm) = {
                        let rot = word & 0x00000f00;
                        let imm = (word & 0x000000ff);
                        let imm = (imm as u32).rotate_right(2 * (rot >> 8));
                        ((word >> 16) as u8 & 0x0f, (word >> 12) as u8 & 0x0f, imm)
                    };
                    if (opcode == 0b0010 || opcode == 0b0100) && Rn == 0b1111 {
                        inst.opcode = Opcode::ADR;
                    }
                    match opcode {
                        0b1101 => {
                            inst.operands = [
                                Operand::Reg(Reg::from_u8(Rd)),
                                Operand::Imm32(imm),
                                Operand::Nothing,
                                Operand::Nothing,
                            ];
                        }
                        _ => {
                            inst.operands = [
                                Operand::Reg(Reg::from_u8(Rd)),
                                Operand::Reg(Reg::from_u8(Rn)),
                                Operand::Imm32(imm),
                                Operand::Nothing,
                            ];
                        }
                    }

                }
                /* ... */
            }
            0b010 => {
                // Load/store word and unsigned byte
                // A5.3
                // Page A5-206
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
                                inst.operands = [
                                    Operand::Reg(Reg::from_u8(Rt)),
                                    Operand::RegDisp(Reg::from_u8(Rn), imm as u16 as i16),
                                    Operand::Nothing,
                                    Operand::Nothing,
                                ];
                                inst.opcode = Opcode::LDR(add, pre, wback);
                                return Ok(());
                            }
                            Opcode::LDR(add, pre, wback)
                        },
                        0b100 => Opcode::STRB(add, pre, wback),
                        0b101 => {
                            if Rn == 0b1111 {
                                inst.operands = [
                                    Operand::Reg(Reg::from_u8(Rt)),
                                    Operand::RegDisp(Reg::from_u8(Rn), imm as u16 as i16),
                                    Operand::Nothing,
                                    Operand::Nothing,
                                ];
                                inst.opcode = Opcode::LDRB(add, pre, wback);
                                return Ok(());
                            }
                            Opcode::LDRB(add, pre, wback)
                        },
                        _ => { unreachable!(); }
                    };
                }
                inst.operands = [
                    Operand::Reg(Reg::from_u8(Rt)),
                    Operand::RegDerefPostindexOffset(Reg::from_u8(Rn), imm as u16),
                    Operand::Nothing,
                    Operand::Nothing,
                ];
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
                    let _Rn = ((word >> 16) & 0x0f) as u8;
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
                    let (Rt, shift) = {
                        let shift = (word & 0xfff) as u16;
                        let word = word >> 12;
                        let Rt = (word & 0xf) as u8;
                        (Rt, shift)
                    };
                    inst.operands = [
                        Operand::Reg(Reg::from_u8(Rt)),
                        Operand::RegDerefRegShift(RegShift::from(shift)),
                        Operand::Nothing,
                        Operand::Nothing,
                    ];
                }
                return Ok(());
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
                    inst.operands = [
                        Operand::Reg(Reg::from_u8(((word >> 16) & 0xf) as u8)),
                        Operand::RegList((word & 0xffff) as u16),
                        Operand::Nothing,
                        Operand::Nothing,
                    ];
                } else if op < 0b110000 {
                    // 10xxxx
                    // the + 1 is to compensate for an architecturally-defined initial offset
                    inst.opcode = Opcode::B;
                    inst.operands = [
                        Operand::BranchOffset(((word & 0x00ffff) + 1) as i16 as i32),
                        Operand::Nothing,
                        Operand::Nothing,
                        Operand::Nothing,
                    ];
                } else {
                    // 11xxxx
                    // the + 1 is to compensate for an architecturally-defined initial offset
                    inst.opcode = Opcode::BL;
                    inst.operands = [
                        Operand::BranchOffset(((word & 0x00ffff) + 1) as i16 as i32),
                        Operand::Nothing,
                        Operand::Nothing,
                        Operand::Nothing,
                    ];
                }
            },
            0b110 | 0b111 => {
                // coprocessor instructions and supervisor call
                // page A5-213
                inst.opcode = Opcode::Incomplete(word);
                return Ok(());
            },
            _ => { unreachable!(); }
        }
        Ok(())
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
    type DecodeError = DecodeError;
    type Decoder = InstDecoder;
    type Operand = Operand;
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
