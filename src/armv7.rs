use std::fmt::{Display, Formatter};

use yaxpeax_arch::{Arch, Decodable, LengthedInstruction};

impl Display for Opcode {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        match self {
            Opcode::Incomplete(word) => { write!(f, "incomplete: {:#x}", word) },
            Opcode::Invalid => { write!(f, "invalid") },
            Opcode::POP => { write!(f, "pop") },
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
    POP,
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

impl Display for Instruction {
    fn fmt(&self, f: &mut Formatter) -> Result<(), std::fmt::Error> {
        fn format_reg_list(f: &mut Formatter, mut list: u16) -> Result<(), std::fmt::Error> {
            write!(f, "{{");
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
                    write!(f, "{}", reg_name(i));
                }
                i += 1;
                list >>= 1;
            }
            write!(f, "}}")
        }

        fn format_shift(f: &mut Formatter, Rm: u8, shift: ShiftSpec) -> Result<(), std::fmt::Error> {
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
                    write!(f, "{}", reg_name(Rm))
                },
                ShiftSpec::Immediate(v) => {
                    let tpe = v & 0x3;
                    let imm = v >> 2;
                    write!(f, "{}, {} {}", reg_name(Rm), shift_tpe_to_str(tpe), imm)
                },
                ShiftSpec::Register(v) => {
                    let tpe = v & 0x3;
                    let Rs = v >> 2;
                    write!(f, "{}, {} {}", reg_name(Rm), shift_tpe_to_str(tpe), reg_name(Rs))
                },
            }
        }

        fn format_reg_shift_mem(f: &mut Formatter, Rd: u8, Rm: u8, shift: ShiftSpec, add: bool, pre: bool, wback: bool) -> Result<(), std::fmt::Error> {
            let op = if add { "" } else { "-" };

            match (pre, wback) {
                (true, true) => {
                    write!(f, "[{}, {}", reg_name(Rd), op)?;
                    format_shift(f, Rm, shift)?;
                    write!(f, "]!")
                },
                (true, false) => {
                    write!(f, "[{}, {}", reg_name(Rd), op)?;
                    format_shift(f, Rm, shift)?;
                    write!(f, "]")
                },
                (false, true) => {
                    unreachable!("I don't know how to render an operand with pre==false and wback==true, this seems like it should be LDRT");
                },
                (false, false) => {
                    write!(f, "[{}], {}", reg_name(Rd), op)?;
                    format_shift(f, Rm, shift)
                }
            }
        }

        fn format_reg_imm_mem(f: &mut Formatter, Rn: u8, imm: u32, add: bool, pre: bool, wback: bool) -> Result<(), std::fmt::Error> {
            if imm != 0 {
                let op = if add { "" } else { "-" };

                match (pre, wback) {
                    (true, true) => {
                        write!(f, "[{}, #{}{:#x}]!", reg_name(Rn), op, imm * 4)
                    },
                    (true, false) => {
                        write!(f, "[{}, #{}{:#x}]", reg_name(Rn), op, imm * 4)
                    },
                    (false, true) => {
                        unreachable!("I don't know how to render an operand with pre==false and wback==true, this seems like it should be LDRT");
                    },
                    (false, false) => {
                        write!(f, "[{}], #{}{:#x}", reg_name(Rn), op, imm * 4)
                    }
                }
            } else {
                match (pre, wback) {
                    (true, true) => {
                        write!(f, "[{}]!", reg_name(Rn))
                    },
                    (true, false) => {
                        write!(f, "[{}]", reg_name(Rn))
                    },
                    (false, true) => {
                        unreachable!("I don't know how to render an operand with pre==false and wback==true, this seems like it should be LDRT");
                    },
                    (false, false) => {
                        write!(f, "[{}]", reg_name(Rn))
                    }
                }
            }
        }
        fn reg_name(num: u8) -> &'static str {
            match num {
                0 => "r0",
                1 => "r1",
                2 => "r2",
                3 => "r3",
                4 => "r4",
                5 => "r5",
                6 => "r6",
                7 => "r7",
                8 => "r8",
                9 => "sb",
                10 => "r10",
                11 => "fp",
                12 => "ip",
                13 => "sp",
                14 => "lr",
                15 => "pc",
                _ => { unreachable!(); }
            }
        }
        match self.opcode {
            Opcode::LDR(true, false, false) => {
                match self.operands {
                    Operands::TwoRegImm(13, Rt, 4) => {
                        return write!(f, "pop{} {{{}}}", self.condition, reg_name(Rt));
                    },
                    _ => {}
                }
            },
            Opcode::STR(false, true, true) => {
                match self.operands {
                    Operands::TwoRegImm(13, Rt, 4) => {
                        return write!(f, "push{} {{{}}}", self.condition, reg_name(Rt));
                    },
                    _ => {}
                }
            },
            Opcode::LDM(true, false, true, _usermode) => {
                // TODO: what indicates usermode in the ARM syntax?
                match self.operands {
                    Operands::RegRegList(13, list) => {
                        write!(f, "pop{} ", self.condition)?;
                        return format_reg_list(f, list);
                    }
                    _ => {}
                }
            }
            Opcode::STM(false, true, true, _usermode) => {
                // TODO: what indicates usermode in the ARM syntax?
                match self.operands {
                    Operands::RegRegList(13, list) => {
                        write!(f, "push{} ", self.condition)?;
                        return format_reg_list(f, list);
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
                        write!(
                            f, "{}{} {}, ",
                            self.opcode,
                            self.condition,
                            reg_name(Rt),
                        )?;
                        return format_reg_imm_mem(f, Rn, imm, add, pre, wback);
                    }
                    // TODO: this might not be necessary
                    Operands::RegImm(Rt, imm) => {
                        write!(
                            f, "{}{} {}, ",
                            self.opcode,
                            self.condition,
                            reg_name(Rt)
                        )?;
                        return format_reg_imm_mem(f, 15, imm, add, pre, wback);
                    },
                    Operands::ThreeOperandWithShift(Rd, Rn, Rm, shift) => {
                        write!(
                            f, "{}{} {}, ",
                            self.opcode,
                            self.condition,
                            reg_name(Rn)
                        )?;
                        return format_reg_shift_mem(f, Rd, Rm, shift, add, pre, wback);
                    }
                    _ => { unreachable!(); }
                }
            }
            Opcode::STM(add, pre, wback, usermode) |
            Opcode::LDM(add, pre, wback, usermode) => {
                match self.operands {
                    Operands::RegRegList(Rr, list) => {
                        write!(
                            f, "{}{} {}{}, ",
                            self.opcode,
                            self.condition,
                            reg_name(Rr),
                            if wback { "!" } else { "" }
                        )?;
                        return format_reg_list(f, list);
                    },
                    _ => { unreachable!(); }
                }
            },
            Opcode::Incomplete(word) => {
                write!(f, "incomplete: {:#x}", word)
            },
            _ => {
                write!(f, "{}{}", self.opcode, self.condition)?;
                match self.operands {
                    Operands::RegisterList(list) => {
                        write!(f, " ")?;
                        format_reg_list(f, list)?;
                    },
                    Operands::TwoOperand(a, b) => {
                        write!(f, " {}, {}", reg_name(a), reg_name(b))?;
                    },
                    Operands::RegImm(a, imm) => {
                        write!(f, " {}, {:#x}", reg_name(a), imm * 4)?;
                    },
                    Operands::RegRegList(r, list) => {
                        write!(f, " {}, ", reg_name(r))?;
                        format_reg_list(f, list)?;
                    },
                    Operands::TwoRegImm(a, b, imm) => {
                        write!(f, " <unimplemented>")?;
                    },
                    Operands::ThreeOperand(a, b, c) => {
                        write!(f, " {}, {}, {}", reg_name(a), reg_name(b), reg_name(c))?;
                    },
                    Operands::ThreeOperandImm(a, b, imm) => {
                        write!(f, " <unimplemented>")?;
                    },
                    Operands::ThreeOperandWithShift(a, b, c, shift) => {
                        write!(f, " {}, {}, ", reg_name(a), reg_name(b))?;
                        format_shift(f, c, shift)?;
                    },
                    Operands::MulThreeRegs(a, b, c) => {
                        write!(f, " {}, {}, {}", reg_name(a), reg_name(b), reg_name(c))?;
                    },
                    Operands::MulFourRegs(a, b, c, d) => {
                        write!(f, " <unimplemented>")?;
                    },
                    Operands::BranchOffset(imm) => {
                        if imm < 0 {
                            write!(f, " $-{:#x}", (-imm) * 4)?;
                        } else {
                            write!(f, " $+{:#x}", imm * 4)?;
                        }
                    }
                };
                Ok(())
            }
        }
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

#[derive(Debug, PartialEq, Eq)]
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
            _ => unsafe {
                // this means the argument `value` must never be outside [0,15]
                // which itself means this function shouldn't be public
                unreachable!();
            }
        }
    }
}

impl Decodable for Instruction {
    fn decode<'a, T: IntoIterator<Item=&'a u8>>(bytes: T) -> Option<Self> {
        let mut blank = Instruction::blank();
        match blank.decode_into(bytes) {
            Some(_) => Some(blank),
            None => None
        }
    }
    fn decode_into<'a, T: IntoIterator<Item=&'a u8>>(&mut self, bytes: T) -> Option<()> {
        fn read_word<'a, T: IntoIterator<Item=&'a u8>>(bytes: T) -> Option<u32> {
            let mut iter = bytes.into_iter();
            let instr: u32 =
                ((*iter.next()? as u32)      ) |
                ((*iter.next()? as u32) << 8 ) |
                ((*iter.next()? as u32) << 16) |
                ((*iter.next()? as u32) << 24);

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
            self.condition = ConditionCode::AL;
            self.opcode = Opcode::Incomplete(word);
            return Some(());
        } else {
            self.condition = ConditionCode::build(cond);
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
                        self.set_S(s);
                        match op {
                            0b000 => {
                                self.opcode = Opcode::MUL;
                                self.operands = Operands::MulThreeRegs(R[3], R[0], R[1]);
                            },
                            0b001 => {
                                self.opcode = Opcode::MLA;
                                self.operands = Operands::MulFourRegs(R[3], R[0], R[1], R[2]);
                            },
                            0b010 => {
                                if s {
                                    self.opcode = Opcode::Invalid;
                                    return None;
                                }
                                self.opcode = Opcode::UMAAL;
                                self.operands = Operands::MulFourRegs(R[2], R[3], R[0], R[1]);
                            },
                            0b011 => {
                                if s {
                                    self.opcode = Opcode::Invalid;
                                    return None;
                                }
                                self.opcode = Opcode::MLS;
                                self.operands = Operands::MulFourRegs(R[3], R[0], R[1], R[2]);
                            }
                            0b100 => {
                                self.opcode = Opcode::UMULL;
                                self.operands = Operands::MulFourRegs(R[2], R[3], R[0], R[1]);
                            }
                            0b101 => {
                                self.opcode = Opcode::UMLAL;
                                self.operands = Operands::MulFourRegs(R[2], R[3], R[0], R[1]);
                            }
                            0b110 => {
                                self.opcode = Opcode::SMULL;
                                self.operands = Operands::MulFourRegs(R[2], R[3], R[0], R[1]);
                            }
                            0b111 => {
                                self.opcode = Opcode::SMLAL;
                                self.operands = Operands::MulFourRegs(R[2], R[3], R[0], R[1]);
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
                            0x00 => {
                    // |c o n d|0 0 0 1|x x x x x x x x x x x x x x x x|1 0 0 1|x x x x|
                                // this is swp or {ld,st}ex, conditional on bit 23
                                match flags {
                                    0b10000 => {
                                        self.opcode = Opcode::SWP;
                                        self.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    },
                                    0b10001 | 0b10010 | 0b10011 => {
                                        self.opcode = Opcode::Invalid;
                                        return None;
                                    }
                                    0b10100 => {
                                        self.opcode = Opcode::SWPB;
                                        self.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    },
                                    0b10101 | 0b10110 | 0b10111 => {
                                        self.opcode = Opcode::Invalid;
                                        return None;
                                    }
                                    0b11000 => {
                                        self.opcode = Opcode::STREX;
                                        self.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    0b11001 => {
                                        self.opcode = Opcode::LDREX;
                                        self.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    0b11010 => {
                                        self.opcode = Opcode::STREXD;
                                        self.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    0b11011 => {
                                        self.opcode = Opcode::LDREXD;
                                        self.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    0b11100 => {
                                        self.opcode = Opcode::STREXB;
                                        self.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    0b11101 => {
                                        self.opcode = Opcode::LDREXB;
                                        self.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    0b11110 => {
                                        self.opcode = Opcode::STREXH;
                                        self.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    0b11111 => {
                                        self.opcode = Opcode::LDREXH;
                                        self.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
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
                            0x01 => {
                    // |c o n d|0 0 0 x|x x x x x x x x x x x x x x x x|1 0 1 1|x x x x|
                    // page A5-201
                                self.opcode = Opcode::Incomplete(word);
                                return Some(());
                                match flags {
                                    0b00010 => {
                                        // self.opcode = Opcode::STRHT_sub;
                                        self.opcode = Opcode::Incomplete(word);
                                        self.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    0b01010 => {
                                        // self.opcode = Opcode::STRHT_add;
                                        self.opcode = Opcode::Incomplete(word);
                                        self.operands = Operands::ThreeOperand(Rn, Rd, LoOffset);
                                    }
                                    0b00110 => {
                                        // self.opcode = Opcode::STRHT_sub;
                                        self.opcode = Opcode::Incomplete(word);
                                        let imm = ((HiOffset << 4) as u16 | LoOffset as u16);
                                        self.operands = Operands::ThreeOperandImm(Rn, Rd, imm);
                                    }
                                    0b01110 => {
                                        // self.opcode = Opcode::STRHT_add;
                                        self.opcode = Opcode::Incomplete(word);
                                        let imm = ((HiOffset << 4) as u16 | LoOffset as u16);
                                        self.operands = Operands::ThreeOperandImm(Rn, Rd, imm);
                                    }
                                    _ => {
                                        unreachable!();
                                    }
                                }
                            }
                            0x10 => {
                    // |c o n d|0 0 0 x|x x x x x x x x x x x x x x x x|1 1 0 1|x x x x|
                    // page A5-201
                                self.opcode = Opcode::Incomplete(word);
                                return Some(());
                            }
                            0x11 => {
                    // |c o n d|0 0 0 x|x x x x x x x x x x x x x x x x|1 1 1 1|x x x x|
                    // page A5-201
                                self.opcode = Opcode::Incomplete(word);
                                return Some(());
                            }
                            _ => { unreachable!(); }
                        }
                    }
                } else {
                    // we know this is data processing with imm or reg shift, OR
                    // misc instructions in Figure A3-4

                    if s == false && opcode >= 0b1000 && opcode < 0b1100 {
                        // the instruction looks like
                        // |c o n d|0 0 0|1 0 x x|0|x x x x|x x x x|x x x x x|x x|x|x x x x|
                        // misc instructions (page A5-194)
                        self.opcode = Opcode::Incomplete(word);
                        return Some(());
                    } else {
                        if opcode >= 16 {
                            unreachable!();
                        }
                        self.opcode = DATA_PROCESSING_OPCODES[opcode as usize];
                        self.set_S(s);

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
                                    self.operands = Operands::TwoOperand(Rd, Rm);
                                } else {
                                    self.operands = Operands::ThreeOperand(Rd, Rn, Rm);
                                }
                            } else {
                                /*
                                 * TODO: look at how this interacts with mov and mvn
                                 */
                                self.operands = Operands::ThreeOperandWithShift(Rd, Rn, Rm, ShiftSpec::Immediate(shift_spec));
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
                                self.opcode = Opcode::Invalid;
                                return None;
                            } else {
                                self.operands = Operands::ThreeOperandWithShift(Rd, Rn, Rm, ShiftSpec::Register(shift_spec));
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
                    self.opcode = Opcode::Incomplete(word);
                    return Some(());
                } else {
                    if opcode >= 16 {
                        unreachable!();
                    }
                    self.opcode = DATA_PROCESSING_OPCODES[opcode as usize];
                    self.set_S(s);

                    let (Rn, imm) = {
                        let imm = word & 0x0000ffff;
                        let word = word >> 16;
                        ((word & 0x0f) as u8, imm)
                    };
                    if (opcode == 0b0010 || opcode == 0b0100) && Rn == 0b1111 {
                        self.opcode = Opcode::ADR;
                    }
                    match opcode {
                        0b1101 => {
                            self.operands = Operands::RegImm(
                                ((word >> 12) & 0xf) as u8,
                                (word & 0x0fff) as u32
                            );
                        }
                        _ => {
                            self.operands = Operands::RegImm(Rn, imm);
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
                    self.opcode = match op {
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
                    self.opcode = match op {
                        0b000 => Opcode::STR(add, pre, wback),
                        0b001 => {
                            if Rn == 0b1111 {
                                self.operands = Operands::RegImm(Rt, imm.into());
                                self.opcode = Opcode::LDR(add, pre, wback);
                                return Some(());
                            }
                            Opcode::LDR(add, pre, wback)
                        },
                        0b100 => Opcode::STRB(add, pre, wback),
                        0b101 => {
                            if Rn == 0b1111 {
                                self.operands = Operands::RegImm(Rt, imm.into());
                                self.opcode = Opcode::LDRB(add, pre, wback);
                                return Some(());
                            }
                            Opcode::LDRB(add, pre, wback)
                        },
                        _ => { unreachable!(); }
                    };
                }
                self.operands = Operands::TwoRegImm(Rn, Rt, imm.into());
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
                        self.opcode = match op {
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
                        self.opcode = match op {
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
                    self.operands = Operands::ThreeOperandWithShift(Rn, Rt, Rm, ShiftSpec::Immediate(shift));
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
                    self.opcode = if (op & 1) == 0 {
                            Opcode::STM(add, pre, wback, usermode)
                        } else {
                            Opcode::LDM(add, pre, wback, usermode)
                        };
                    self.operands = Operands::RegRegList(
                        ((word >> 16) & 0xf) as u8,
                        (word & 0xffff) as u16
                    );
                } else if op < 0b110000 {
                    // 10xxxx
                    // the + 1 is to compensate for an architecturally-defined initial offset
                    self.opcode = Opcode::B;
                    self.operands = Operands::BranchOffset(((word & 0x00ffff) + 1) as i16 as i32);
                } else {
                    // 11xxxx
                    // the + 1 is to compensate for an architecturally-defined initial offset
                    self.opcode = Opcode::BL;
                    self.operands = Operands::BranchOffset(((word & 0x00ffff) + 1) as i16 as i32);
                }
            },
            0b110 | 0b111 => {
                // coprocessor instructions and supervisor call
                // page A5-213
                self.opcode = Opcode::Incomplete(word);
                return Some(());
            },
            _ => { unreachable!(); }
        }
        Some(())
    }
}

pub struct ARMv7;
impl Arch for ARMv7 {
    type Address = u32;
    type Instruction = Instruction;
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
