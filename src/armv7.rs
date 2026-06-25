/// Manual references in this crate, both figure and page numbers, are with respect to the document
/// `DDI0406C_d_armv7ar_arm.pdf`
/// `sha256: 294668ae6480133b32d85e9567cc77c5eb0e1232decdf42cac7ab480e884f6e0`

//#[cfg(feature="use-serde")]
//use serde::{Serialize, Deserialize};

use core::fmt::{self, Display, Formatter};

use yaxpeax_arch::{Arch, AddressDiff, Decoder, LengthedInstruction, Reader, ReadError};
#[allow(deprecated)]
use yaxpeax_arch::{NoColors, ShowContextual};

mod thumb;
// #[cfg(feature = "fmt")]
mod display;

#[cfg(all(feature="alloc", feature="fmt"))]
pub use display::InstructionTextBuffer;

// opcode, s, w, cond
/// a struct for the combined display of an opcode and possible suffixes.
///
/// this includes the opcode, its optional `.s` suffix, optional `.w` suffix, and condition code,
/// if any.
pub struct ConditionedOpcode(pub Opcode, pub bool, pub bool, pub ConditionCode);

impl Display for ConditionedOpcode {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}{}", self.0, if self.1 { "s" } else { "" }, if self.2 { ".w" } else { "" }, self.3)
    }
}

/// a context impl to display `arm` instructions with no additional context (no symbol name
/// information, offset names, etc). this impl results in `some_instruction.contextualize(...)`
/// displaying an instruction the same way its `Display` impl would.
pub struct NoContext;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[allow(non_camel_case_types)]
#[allow(missing_docs)]
#[cfg_attr(feature = "non-exhaustive-enums", non_exhaustive)]
pub enum Opcode {
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
    LDR,
    STR,
    LDRH,
    STRH,
    LDRB,
    STRB,
    LDRSH,
    LDRSHT,
    LDRSB,
    LDRSBT,
    STRD,
    LDRD,
    LDC(u8, bool),
    LDCL(u8, bool),
    STC(u8, bool),
    STCL(u8, bool),
    MCRR(u8, u8, bool),
    MRRC(u8, u8, bool),
    /// > MCR (Move to Coprocessor from ARM Register)
    ///
    /// fields here are `coproc`, `opcode_1`, `opcode_2`, and a bool indicating if the original
    /// encoding was `MCR` or `MCR2` (`true` means `MCR2`).
    MCR(u8, u8, u8, bool),
    /// > MRC (Move to ARM Register from Coprocessor)
    ///
    /// fields here are `coproc`, `opcode_1`, `opcode_2`, and a bool indicating if the original
    /// encoding was `MRC` or `MRC2` (`true` means `MRC2`).
    MRC(u8, u8, u8, bool),
    CDP(u8, u8, u8, bool),
    SRS(bool, bool),
    RFE(bool, bool),
    LDRT,
    STRT,
    LDRHT,
    STRHT,
    LDRBT,
    STRBT,
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
    ERET,
    BKPT,
    HVC,
    SMC,
    MOVT,
    QDSUB,
    QDADD,
    QSUB,
    QADD,

    TBB,
    TBH,
    UDF,
    SVC,
    WFE,
    WFI,
    SEV,
    CSDB,
    YIELD,
    HINT,
    NOP,
    LEAVEX,
    ENTERX,
    CLREX,
    DSB,
    DMB,
    ISB,
    SXTH,
    UXTH,
    SXTB16,
    UXTB16,
    SXTB,
    UXTB,
    SXTAH,
    UXTAH,
    SXTAB16,
    UXTAB16,
    SXTAB,
    UXTAB,
    CBZ,
    CBNZ,
    SETEND,
    CPS(bool),
    CPS_modeonly,
    REV,
    REV16,
    REVSH,
    IT,

    PKHTB,
    PKHBT,
    ORN,
    SSAT,
    SSAT16,
    SBFX,
    USAT,
    USAT16,
    UBFX,
    BFI,
    BFC,
    DBG,
    PLD,
    PLI,
    RBIT,
    SEL,

    SADD16,
    QADD16,
    SHADD16,
    SASX,
    QASX,
    SHASX,
    SSAX,
    QSAX,
    SHSAX,
    SSUB16,
    QSUB16,
    SHSUB16,
    SADD8,
    QADD8,
    SHADD8,
    SSUB8,
    QSUB8,
    SHSUB8,
    UADD16,
    UQADD16,
    UHADD16,
    UASX,
    UQASX,
    UHASX,
    USAX,
    UQSAX,
    UHSAX,
    USUB16,
    UQSUB16,
    UHSUB16,
    UADD8,
    UQADD8,
    UHADD8,
    USUB8,
    UQSUB8,
    UHSUB8,

    SMLSD,
    SMMLA,
    SMMLS,
    USADA8,
    USAD8,
    SMLAD,
    SMUSD,
    SMMUL,
    SMULW(bool),
    SMUAD,
    SDIV,
    UDIV,
    SMLALD(bool),
    SMLSLD(bool),
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

/// a struct describiing a shifted register operand. this is primarily interesting in that it can
/// be translated to a `RegShiftStyle` for further interpretation.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
#[repr(transparent)]
pub struct RegShift {
    data: u16
}

impl RegShift {
    /// convert an instruction's `RegShift` operand into something more appropriate for
    /// programmatic use.
    pub fn into_shift(&self) -> RegShiftStyle {
        if self.data & 0b10000 == 0 {
            RegShiftStyle::RegImm(RegImmShift { data: self.data })
        } else {
            RegShiftStyle::RegReg(RegRegShift { data: self.data })
        }
    }

    /// Does this shift actually do anything?
    fn is_noop(&self) -> bool {
        match self.into_shift() {
            RegShiftStyle::RegImm(shift) => shift.is_noop(),
            // We can't know statically that this is a no-op, because the final result is based on
            // register data. Therefore, consider it a live shift.
            RegShiftStyle::RegReg(_) => false,
        }
    }

    /// don't use this. it's for armv7 testing only.
    #[doc(hidden)]
    pub fn from_raw(data: u16) -> Self {
        RegShift { data }
    }
}

/// an enum describing one of two ways a shifted register operand may be shifted.
pub enum RegShiftStyle {
    /// a register shifted by an immediate.
    RegImm(RegImmShift),
    /// a register shifted by a register.
    RegReg(RegRegShift),
}

/// a register shifted by a register.
#[repr(transparent)]
pub struct RegRegShift {
    data: u16
}

/// the way a shift operation is carried out.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum ShiftStyle {
    /// left-shift the value, filling in zeroes.
    LSL = 0,
    /// right-shift the value, filling in zeroes.
    LSR = 1,
    /// arithmetic shift right, filling with the top bit of the value (sign-extending).
    ASR = 2,
    /// rotate-right, filling with bits shifted out of the value.
    ROR = 3,
    /// shift right by one, populating the new most-significant bit from the carry flag.
    ///
    /// only possible on immediate shifts.
    RRX = 4,
}

impl Display for ShiftStyle {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use core::fmt::Write;
        let name = self.name();
        f.write_char(name[0] as char)?;
        f.write_char(name[1] as char)?;
        f.write_char(name[2] as char)?;
        Ok(())
    }
}

impl ShiftStyle {
    fn from_bits(bits: u8) -> ShiftStyle {
        match bits {
            0b00 => ShiftStyle::LSL,
            0b01 => ShiftStyle::LSR,
            0b10 => ShiftStyle::ASR,
            0b11 => ShiftStyle::ROR,
            _ => unreachable!("bad ShiftStyle index")
        }
    }

    fn name(&self) -> &'static [u8; 3] {
        match self {
            ShiftStyle::LSL => b"lsl",
            ShiftStyle::LSR => b"lsr",
            ShiftStyle::ASR => b"asr",
            ShiftStyle::ROR => b"ror",
            ShiftStyle::RRX => b"rrx",
        }
    }
}

impl RegRegShift {
    /// the general-purpose register, an amount to shift the shiftee.
    pub fn shifter(&self) -> Reg {
        Reg::from_u8((self.data >> 8) as u8 & 0b1111)
    }
    /// the way in which this register is shifted.
    pub fn stype(&self) -> ShiftStyle {
        ShiftStyle::from_bits((self.data >> 5) as u8 & 0b11)
    }
    /// the general-purpose register to be shifted.
    pub fn shiftee(&self) -> Reg {
        Reg::from_u8(self.data as u8 & 0b1111)
    }
}

/// a register shifted by an immediate.
#[repr(transparent)]
pub struct RegImmShift {
    data: u16
}

impl RegImmShift {
    /// The shift immediate, without any interpretation
    fn imm_raw(&self) -> u8 {
        (self.data >> 7) as u8 & 0b11111
    }

    /// the immediate this register is shifted by.
    pub fn imm(&self) -> u8 {
        let raw = self.imm_raw();
        // in the ARMv7m reference,
        // `Instruction Details` ->
        //   `Shifts applied to a register` ->
        //      `Constant shifts`:
        //
        // > The assembler encodes <shift> into two type bits and five immediate bits, as follows:
        // > ...
        // > LSR #<n>    type = 0b01
        // >             If <n> < 32, immediate = <n>.
        // >             If <n> == 32, immediate = 0.
        // > ASR #<n>    type = 0b10
        // >             If <n> < 32, immediate = <n>.
        // >             If <n> == 32, immediate = 0.
        // > ...
        // > ROR #<n>    type = 0b11, immediate = <n>.
        // > RRX         type = 0b11, immediate = 0.
        //
        // so we have to fix this up here.
        if raw == 0 {
            let stype = self.stype();
            if stype == ShiftStyle::LSR || stype == ShiftStyle::ASR {
                return 32;
            } else if stype == ShiftStyle::ROR {
                // this is actually RRX, which rotates by exactly one bit.
                return 1;
            }
        }
        raw
    }

    /// the way in which this register is shifted.
    pub fn stype(&self) -> ShiftStyle {
        let stype = ShiftStyle::from_bits((self.data >> 5) as u8 & 0b11);

        if self.imm_raw() == 0 && stype == ShiftStyle::ROR {
            ShiftStyle::RRX
        } else {
            stype
        }
    }

    /// the general-purpose register to be shifted.
    pub fn shiftee(&self) -> Reg {
        Reg::from_u8(self.data as u8 & 0b1111)
    }

    /// Does this shift actually do anything?
    fn is_noop(&self) -> bool {
        self.stype() == ShiftStyle::LSL && self.imm() == 0
    }
}

/// a struct describing an `arm` register.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct Reg {
    bits: u8
}

impl Reg {
    #[allow(non_snake_case)]
    fn from_sysm(R: bool, M: u8) -> Option<Operand> {
/*
 * Is one of:
 * • <Rm>_<mode>, encoded with R==0.
 * • ELR_hyp, encoded with R==0.
 * • SPSR_<mode>, encoded with R==1.
 * For a full description of the encoding of this field, see Encoding and use of Banked register
 * transfer
 * instructions on page B9-1959.
 * */
        if R == false {
            [
                Some(Operand::BankedReg(Bank::Usr, Reg::from_u8(8))),
                Some(Operand::BankedReg(Bank::Usr, Reg::from_u8(9))),
                Some(Operand::BankedReg(Bank::Usr, Reg::from_u8(10))),
                Some(Operand::BankedReg(Bank::Usr, Reg::from_u8(11))),
                Some(Operand::BankedReg(Bank::Usr, Reg::from_u8(12))),
                Some(Operand::BankedReg(Bank::Usr, Reg::from_u8(13))),
                Some(Operand::BankedReg(Bank::Usr, Reg::from_u8(14))),
                None,
                Some(Operand::BankedReg(Bank::Fiq, Reg::from_u8(8))),
                Some(Operand::BankedReg(Bank::Fiq, Reg::from_u8(9))),
                Some(Operand::BankedReg(Bank::Fiq, Reg::from_u8(10))),
                Some(Operand::BankedReg(Bank::Fiq, Reg::from_u8(11))),
                Some(Operand::BankedReg(Bank::Fiq, Reg::from_u8(12))),
                Some(Operand::BankedReg(Bank::Fiq, Reg::from_u8(13))),
                Some(Operand::BankedReg(Bank::Fiq, Reg::from_u8(14))),
                None,
                Some(Operand::BankedReg(Bank::Irq, Reg::from_u8(13))),
                Some(Operand::BankedReg(Bank::Irq, Reg::from_u8(14))),
                Some(Operand::BankedReg(Bank::Svc, Reg::from_u8(13))),
                Some(Operand::BankedReg(Bank::Svc, Reg::from_u8(14))),
                Some(Operand::BankedReg(Bank::Abt, Reg::from_u8(13))),
                Some(Operand::BankedReg(Bank::Abt, Reg::from_u8(14))),
                Some(Operand::BankedReg(Bank::Und, Reg::from_u8(13))),
                Some(Operand::BankedReg(Bank::Und, Reg::from_u8(14))),
                None,
                None,
                None,
                None,
                Some(Operand::BankedReg(Bank::Mon, Reg::from_u8(13))),
                Some(Operand::BankedReg(Bank::Mon, Reg::from_u8(14))),
                Some(Operand::BankedReg(Bank::Hyp, Reg::from_u8(13))),
                Some(Operand::BankedReg(Bank::Hyp, Reg::from_u8(14))),
            ][M as usize]
        } else {
            if M == 0b01110 {
                Some(Operand::BankedSPSR(Bank::Fiq))
            } else if M == 0b10000 {
                Some(Operand::BankedSPSR(Bank::Irq))
            } else if M == 0b10010 {
                Some(Operand::BankedSPSR(Bank::Svc))
            } else if M == 0b10100 {
                Some(Operand::BankedSPSR(Bank::Abt))
            } else if M == 0b10110 {
                Some(Operand::BankedSPSR(Bank::Und))
            } else if M == 0b11100 {
                Some(Operand::BankedSPSR(Bank::Mon))
            } else if M == 0b11110 {
                Some(Operand::BankedSPSR(Bank::Hyp))
            } else {
                None
            }
        }
    }

    /// create a new `Reg` with the specified number.
    ///
    /// panics if `bits` is out of range (16 or above).
    #[inline]
    pub fn from_u8(bits: u8) -> Reg {
        if bits > 0b1111 {
            panic!("register number out of range");
        }

        Reg { bits }
    }

    /// get the number of this register. the returned value will be between 0 and 15.
    pub fn number(&self) -> u8 {
        self.bits
    }
}

/// a control register.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct CReg {
    bits: u8
}

impl Display for CReg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "c{}", self.bits)
    }
}

impl CReg {
    /// create a new `CReg` with the specified number.
    ///
    /// panics if `bits` is out of range (16 or above).
    #[inline]
    pub fn from_u8(bits: u8) -> CReg {
        if bits > 0b1111 {
            panic!("register number out of range");
        }

        CReg { bits }
    }

    /// get the number of this register. the returned value will be between 0 and 15.
    pub fn number(&self) -> u8 {
        self.bits
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(non_camel_case_types)]
#[allow(missing_docs)]
pub enum StatusRegMask {
    // Note 0b0000 is unused (as is 0b10000)
    CPSR_C = 0b0001,
    CPSR_X = 0b0010,
    CPSR_XC = 0b0011,
    APSR_G = 0b0100,
    CPSR_SC = 0b0101,
    CPSR_SX = 0b0110,
    CPSR_SXC = 0b0111,
    APSR_NZCVQ = 0b1000,
    CPSR_FC = 0b1001,
    CPSR_FX = 0b1010,
    CPSR_FXC = 0b1011,
    APSR_NZCVQG = 0b1100,
    CPSR_FSC = 0b1101,
    CPSR_FSX = 0b1110,
    CPSR_FSXC = 0b1111,
    SPSR = 0b10000,
    SPSR_C = 0b10001,
    SPSR_X = 0b10010,
    SPSR_XC = 0b10011,
    SPSR_S = 0b10100,
    SPSR_SC = 0b10101,
    SPSR_SX = 0b10110,
    SPSR_SXC = 0b10111,
    SPSR_F = 0b11000,
    SPSR_FC = 0b11001,
    SPSR_FX = 0b11010,
    SPSR_FXC = 0b11011,
    SPSR_FS = 0b11100,
    SPSR_FSC = 0b11101,
    SPSR_FSX = 0b11110,
    SPSR_FSXC = 0b11111,
}

impl StatusRegMask {
    fn from_raw(raw: u8) -> Result<StatusRegMask, DecodeError> {
        if raw == 0 {
            // invalid status reg mask value
            return Err(DecodeError::InvalidOperand);
        }
        Ok([
            StatusRegMask::CPSR_C, // actually unreachable
            StatusRegMask::CPSR_C,
            StatusRegMask::CPSR_X,
            StatusRegMask::CPSR_XC,
            StatusRegMask::APSR_G,
            StatusRegMask::CPSR_SC,
            StatusRegMask::CPSR_SX,
            StatusRegMask::CPSR_SXC,
            StatusRegMask::APSR_NZCVQ,
            StatusRegMask::CPSR_FC,
            StatusRegMask::CPSR_FX,
            StatusRegMask::CPSR_FXC,
            StatusRegMask::APSR_NZCVQG,
            StatusRegMask::CPSR_FSC,
            StatusRegMask::CPSR_FSX,
            StatusRegMask::CPSR_FSXC,
            StatusRegMask::SPSR,
            StatusRegMask::SPSR_C,
            StatusRegMask::SPSR_X,
            StatusRegMask::SPSR_XC,
            StatusRegMask::SPSR_S,
            StatusRegMask::SPSR_SC,
            StatusRegMask::SPSR_SX,
            StatusRegMask::SPSR_SXC,
            StatusRegMask::SPSR_F,
            StatusRegMask::SPSR_FC,
            StatusRegMask::SPSR_FX,
            StatusRegMask::SPSR_FXC,
            StatusRegMask::SPSR_FS,
            StatusRegMask::SPSR_FSC,
            StatusRegMask::SPSR_FSX,
            StatusRegMask::SPSR_FSXC,
        ][raw as usize])
    }
}

/// an operand in an `arm` instruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "non-exhaustive-enums", non_exhaustive)]
pub enum Operand {
    /// a general-purpose register.
    Reg(Reg),
    /// a general-purpose register, with writeback. these generally imply an increment by width of
    /// a memort operand, depending on the instruction.
    RegWBack(Reg, bool),
    /// a list of registers specified as a bitmask from bits 0 to 15.
    RegList(u16),
    /// a memory access, dereferencing a general-purpose register.
    RegDeref(Reg),
    /// a memory access, dereferencing a shifted general-purpose register with register or
    /// immediate offset.
    RegShift(RegShift),
    /// a memory access of a register, post-indexed a register shifted by register or immediate.
    /// the first bool indicates if the shifted-register is added or subtracted ot the base
    /// register, while the second bool indicates if the resulting address is written back to the
    /// base register.
    RegDerefPostindexRegShift(Reg, RegShift, bool, bool), // add/sub, wback
    /// a memory access of a register, pre-indexed with a register shifted by register or
    /// immediate. the first bool indicates if the shifted-register is added or subtracted ot the
    /// base register, while the second bool indicates if the resulting address is written back to
    /// the base register.
    RegDerefPreindexRegShift(Reg, RegShift, bool, bool), // add/sub, wback
    /// a memory access of a register, post-indexed with an immediate. the first bool indicates if
    /// the shifted-register is added or subtracted ot the base register, while the second bool
    /// indicates if the resulting address is written back to the base register.
    RegDerefPostindexOffset(Reg, u16, bool, bool), // add/sub, wback
    /// a memory access of a register, pre-indexed with an immediate. the first bool indicates if
    /// the shifted-register is added or subtracted ot the base register, while the second bool
    /// indicates if the resulting address is written back to the base register.
    RegDerefPreindexOffset(Reg, u16, bool, bool), // add/sub, wback
    /// a memory access of a register, post-indexed with a register. the first bool indicates if the
    /// shifted-register is added or subtracted ot the base register, while the second bool
    /// indicates if the resulting address is written back to the base register.
    RegDerefPostindexReg(Reg, Reg, bool, bool), // add/sub, wback
    /// a memory access of a register, pre-indexed with a register. the first bool indicates if the
    /// shifted-register is added or subtracted ot the base register, while the second bool
    /// indicates if the resulting address is written back to the base register.
    RegDerefPreindexReg(Reg, Reg, bool, bool), // add/sub, wback
    /// a 12-bit immediate, stored in a `u16`.
    Imm12(u16),
    /// a 32-bit immediate, stored in a `u32`.
    Imm32(u32),
    /// a pc-relative branch, with 32-bit signed offset, left-shifted by 2.
    BranchOffset(i32),
    /// a pc-relative branch, with 32-bit signed offset, left-shifted by 1.
    BranchThumbOffset(i32),
    /// a coprocessor index.
    #[deprecated(
        since = "0.3.2",
        note = "`Coprocessor` was prematurely added: `CoprocOption` the operand used to indicate \
                coprocessor selection and has always been the variant used as such"
    )]
    Coprocessor(u8),
    /// a coprocessor option number.
    CoprocOption(u8),
    /// an `arm` control register.
    CReg(CReg),
    /// an `arm` banked register, either `usr` (general-purpose) bank or one of the alternate sets
    /// of `arm` registers.
    BankedReg(Bank, Reg),
    /// `spsr` in some `arm` register bank.
    BankedSPSR(Bank),
    /// a mask of bits for the `spsr` register.
    StatusRegMask(StatusRegMask),
    /// the `apsr` register.
    APSR,
    /// the `spsr` register.
    SPSR,
    /// the `cpsr` register.
    CPSR,
    /// "no operand". since an instruction's `operands` array is always four entries, this is used
    /// to fill space, if any, after recording an instruction's extant operands.
    Nothing,
}

/// a trait describing functions in support of processing operands
///
/// this is interesting more for future implementation of `yaxpeax-arm`: operands currently are
/// backed by an `Operand` enum, which means that operating on an operand involves potentially more
/// copies and data management than strictly necessary. in the future, operands may be described
/// more granularly, where `OperandVisitor` is the stable interface to the pre-enum constituent
/// parts of operands.
///
/// see `yaxpeax-x86`'s equivalent trait for examples of that direction.
pub trait OperandVisitor {
    /// the result for successful processing of an operand. for formatting, as an example, this is
    /// likely `()`.
    type Ok;
    /// the result for an error in processing an operand.
    type Error;

    /// process an operand that is a simple general purpose register.
    fn visit_reg(&mut self, reg: Reg) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is a simple general purpose register with writeback.
    fn visit_reg_wback(&mut self, reg: Reg, wback: bool) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is a list of registers.
    fn visit_reglist(&mut self, list: u16) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is a memory access through a general purpose register.
    fn visit_reg_deref(&mut self, reg: Reg) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is a shifted general pupose register.
    fn visit_reg_shift(&mut self, reg_shift: RegShift) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is the dereference of a register, afterward incremented by index.
    fn visit_reg_deref_postindex_reg_shift(&mut self, base: Reg, index: RegShift, add: bool, wback: bool) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is the dereference of a register incremented by index.
    fn visit_reg_deref_preindex_reg_shift(&mut self, base: Reg, index: RegShift, add: bool, wback: bool) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is the dereference of a register, afterward incremented by offset.
    fn visit_reg_deref_postindex_offset(&mut self, base: Reg, offset: u16, add: bool, wback: bool) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is the dereference of a register incremented by offset.
    fn visit_reg_deref_preindex_offset(&mut self, base: Reg, offset: u16, add: bool, wback: bool) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is the dereference of a register, afterward incremented by offset.
    fn visit_reg_deref_postindex_reg(&mut self, base: Reg, offset: Reg, add: bool, wback: bool) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is the dereference of a register incremented by offset.
    fn visit_reg_deref_preindex_reg(&mut self, base: Reg, offset: Reg, add: bool, wback: bool) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is a 12-bit immediate.
    fn visit_imm12(&mut self, imm: u16) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is a 32-bit immediate.
    fn visit_imm32(&mut self, imm: u32) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is a branch with i32 offset.
    fn visit_branch_offset(&mut self, offset: i32) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is a branch with i32 offset that also exchanges instruction sets.
    ///
    /// this is typically rendered in the same way as `visit_branch_offset` but is a distinct
    /// helper due to support uses emphasizing the ISA-changing behavior.
    fn visit_blx_offset(&mut self, offset: i32) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is a coprocessor option access. not exactly clear what this means,
    /// this may need to get foled into an opcode or redefinition of the operand.
    fn visit_coprocessor_option(&mut self, nr: u8) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is a control register.
    fn visit_creg(&mut self, creg: CReg) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is a banked register.
    fn visit_banked_reg(&mut self, bank: Bank, reg: u16) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is a banked version of `SPSR`.
    fn visit_banked_spsr(&mut self, bank: Bank) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is some set of bits out of a status register.
    fn visit_status_reg_mask(&mut self, mask: StatusRegMask) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is `APSR`.
    fn visit_apsr(&mut self) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is `SPSR`.
    fn visit_spsr(&mut self) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is `CPSR`.
    fn visit_cpsr(&mut self) -> Result<Self::Ok, Self::Error>;
    /// process an operand that is not defined above. there are no parameters as for an unknown
    /// operand kind there is no appropriate tuple of values to provide.
    fn visit_other(&mut self) -> Result<Self::Ok, Self::Error>;
}

/// a register bank for a register in `armv7` or below.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Bank {
    Usr,
    Fiq,
    Irq,
    Svc,
    Abt,
    Und,
    Mon,
    Hyp,
}

/// a `armv7` or below instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Instruction {
    /// the condition code for this instruction, defaults to `AL` if the instruction is
    /// unconditional.
    pub condition: ConditionCode,
    /// the opcode of this instruction.
    pub opcode: Opcode,
    /// operands for the decoded instruction. operands are populated from index 0, to 1, 2, and 3.
    /// operands from the instruction are non-`Operand::Nothing`.
    pub operands: [Operand; 4],
    /// does this instruction update flags, while variants that do not update flags exist?
    pub s: bool,
    /// is this a 32-bit thumb instruction?
    pub wide: bool,
    /// and if it is a 32-bit thumb instruction, should the .w suffix be shown?
    pub thumb_w: bool,
    /// and generally speaking, was this just a thumb-encoded instruction?
    pub thumb: bool,
}

/// the kinds of errors possibly encountered in trying to decode an `armv7` or below instruction.
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum DecodeError {
    /// the input was insufficient to decode a full instruction. for non-thumb instructions, this means
    /// the input was not at least four bytes long. for thumb instructions, the input was either
    /// not two bytes, or not four bytes, depending on how much the instruction would need.
    ExhaustedInput,
    /// the instruction encodes an opcode that is not valid.
    InvalidOpcode,
    /// the instruction encodes an operand that is not valid.
    InvalidOperand,
    /// `yaxpeax-arm` doesn't know how to decode this, but it may be a valid instruction. the
    /// instruction decoder is not complete, sorry. :(
    ///
    /// in practice this typically indicates some kinds of coprocessor instruction, or `ARMv7` SIMD
    /// instruction.
    Incomplete,
    /// the instruction includes reserved bits that were not set as required.
    Nonconforming,
    /// the input encodes an instruction that is explicitly undefined.
    Undefined,
    /// the input encodes an instruction with unpredictable behavior.
    Unpredictable,
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
    fn bad_operand(&self) -> bool {
        self == &DecodeError::InvalidOperand || self == &DecodeError::Unpredictable
    }
    fn description(&self) -> &'static str {
        match self {
            DecodeError::ExhaustedInput => "exhausted input",
            DecodeError::InvalidOpcode => "invalid opcode",
            DecodeError::InvalidOperand => "invalid operand",
            DecodeError::Incomplete => "incomplete decoder",
            DecodeError::Nonconforming => "invalid reserved bits",
            DecodeError::Undefined => "undefined encoding",
            DecodeError::Unpredictable => "unpredictable instruction",
        }
    }
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
            s: false,
            thumb_w: false,
            wide: false,
            thumb: false,
        }
    }
}

impl Instruction {
    fn set_s(&mut self, value: bool) {
        self.s = value;
    }
    /// does this instruction set status flags?
    pub fn s(&self) -> bool { self.s }
    pub(crate) fn set_w(&mut self, value: bool) {
        self.thumb_w = value;
    }
    /// was this instruction encoded in `thumb` mode and still 4 bytes, *and* requires a `.w`
    /// suffix on the opcode?
    pub fn w(&self) -> bool { self.thumb_w }
    pub(crate) fn set_wide(&mut self, value: bool) {
        self.wide = value;
    }
    /// was this instruction encoded in `thumb` mode and still 4 bytes?
    pub fn wide(&self) -> bool { self.wide }
    pub(crate) fn set_thumb(&mut self, value: bool) {
        self.thumb = value;
    }
    /// was this instruction encoded in `thumb` mode?
    pub fn thumb(&self) -> bool { self.thumb }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        #[allow(deprecated)]
        self.contextualize(&NoColors, 0, Some(&NoContext), f)
    }
}

impl LengthedInstruction for Instruction {
    type Unit = AddressDiff<<ARMv7 as Arch>::Address>;
    fn min_size() -> Self::Unit {
        // TODO: this is contingent on the decoder mode...
        AddressDiff::from_const(4)
    }
    fn len(&self) -> Self::Unit {
        if self.thumb && !self.wide {
            AddressDiff::from_const(2)
        } else {
            AddressDiff::from_const(4)
        }
    }
}

/// a condition code for am `armv7` or below instruction.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
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

impl ConditionCode {
    fn name(&self) -> &'static [u8; 2] {
        match self {
            ConditionCode::EQ => &[b'e', b'q'],
            ConditionCode::NE => &[b'n', b'e'],
            ConditionCode::HS => &[b'h', b's'],
            ConditionCode::LO => &[b'l', b'o'],
            ConditionCode::MI => &[b'm', b'i'],
            ConditionCode::PL => &[b'p', b'l'],
            ConditionCode::VS => &[b'v', b's'],
            ConditionCode::VC => &[b'v', b'c'],
            ConditionCode::HI => &[b'h', b'i'],
            ConditionCode::LS => &[b'l', b's'],
            ConditionCode::GE => &[b'g', b'e'],
            ConditionCode::LT => &[b'l', b't'],
            ConditionCode::GT => &[b'g', b't'],
            ConditionCode::LE => &[b'l', b'e'],
            ConditionCode::AL => &[b'a', b'l'],
        }
    }
}

impl Display for ConditionCode {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        if *self != ConditionCode::AL {
            use core::fmt::Write;
            f.write_char(self.name()[0] as char)?;
            f.write_char(self.name()[1] as char)?;
        }

        Ok(())
    }
}

impl ConditionCode {
    #[inline]
    fn build(value: u8) -> ConditionCode {
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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[allow(dead_code)]
enum DecodeMode {
    User,
    FIQ,
    IRQ,
    Supervisor,
    Monitor,
    Abort,
    Hyp,
    Undefined,
    System,
    /// Catch-all mode to try decoding all ARM instructions. Some instructions are `UNDEFINED` or
    /// `UNPREDICTABLE` in some modes, but `Any` will attempt to decode all.
    Any,
}

impl Default for DecodeMode {
    fn default() -> Self {
        DecodeMode::Any
    }
}

impl DecodeMode {
    fn is_user(&self) -> bool {
        match self {
            DecodeMode::Any |
            DecodeMode::User => true,
            _ => false
        }
    }
    #[allow(dead_code)]
    fn is_supervisor(&self) -> bool {
        match self {
            DecodeMode::Any |
            DecodeMode::Supervisor => true,
            _ => false
        }
    }
    fn is_hyp(&self) -> bool {
        match self {
            DecodeMode::Any |
            DecodeMode::Hyp => true,
            _ => false
        }
    }
    fn is_system(&self) -> bool {
        match self {
            DecodeMode::Any |
            DecodeMode::System => true,
            _ => false
        }
    }
    fn is_any(&self) -> bool {
        match self {
            DecodeMode::Any => true,
            _ => false,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
#[allow(non_camel_case_types)]
enum ARMVersion {
    v4,
    v5,
    v6,
    v6t2,
    v7,
    v7ve,
    v7vese,
    Any,
}

impl Default for ARMVersion {
    fn default() -> Self {
        ARMVersion::Any
    }
}

// nothing checks/rejects by arm version yet, but.. soon....
/// a struct with decode configuration for `ARMv7` and below. the same decoder is used for `thumb`
/// and non-`thumb` modes, and the same instruction struct is used for decoded instructions in
/// either mode.
///
/// NOTE: helper functions here create `InstDecoder` for specific revisions, extensions, or lack
/// thereof, in the supported instruction set. `yaxpeax-arm` does not actually honor these settings
/// yet. this means any `InstDecoder` will decode all known instructions through the latest `ARMv7`
/// extensions.
#[allow(unused)]
#[derive(Debug)]
pub struct InstDecoder {
    mode: DecodeMode,
    version: ARMVersion,
    should_is_must: bool,
    thumb: bool,
}

impl Default for InstDecoder {
    fn default() -> Self {
        Self {
            mode: DecodeMode::Any,
            version: ARMVersion::Any,
            should_is_must: true,
            thumb: false,
        }
    }
}

impl InstDecoder {
    /// set the decoder to decoding in thumb mode as the specified bool provides; `true` means
    /// "yes, decode in `thumb` mode", where `false` means to decode as a normal `arm` instruction.
    pub fn set_thumb_mode(&mut self, thumb: bool) {
        self.thumb = thumb;
    }

    /// set the decoder to decoding in thumb mode as the specified bool provides; `true` means
    /// "yes, decode in `thumb` mode", where `false` means to decode as a normal `arm` instruction.
    ///
    /// (this consumes and returns the `InstDecoder` to support use in chained calls.)`
    pub fn with_thumb_mode(mut self, thumb: bool) -> Self {
        self.set_thumb_mode(thumb);
        self
    }

    /// returns whether the decoder is currently set to decode in Thumb mode
    pub fn in_thumb_mode(&self) -> bool {
        self.thumb
    }

    /// initialize a new `arm` `InstDecoder` with default ("everything") support, but in `thumb`
    /// mode.
    pub fn default_thumb() -> Self {
        Self::default().with_thumb_mode(true)
    }

    /// create an `InstDecoder` that supports only instructions through to `ARMv4`.
    pub fn armv4() -> Self {
        Self {
            mode: DecodeMode::Any,
            version: ARMVersion::v4,
            should_is_must: true,
            thumb: false,
        }
    }

    /// create an `InstDecoder` that supports only instructions through to `ARMv5`.
    pub fn armv5() -> Self {
        Self {
            mode: DecodeMode::Any,
            version: ARMVersion::v5,
            should_is_must: true,
            thumb: false,
        }
    }

    /// create an `InstDecoder` that supports only instructions through to `ARMv6`.
    pub fn armv6() -> Self {
        Self {
            mode: DecodeMode::Any,
            version: ARMVersion::v6,
            should_is_must: true,
            thumb: false,
        }
    }

    /// create an `InstDecoder` that supports only instructions through to `ARMv6t2`.
    pub fn armv6t2() -> Self {
        Self {
            mode: DecodeMode::Any,
            version: ARMVersion::v6t2,
            should_is_must: true,
            thumb: false,
        }
    }

    /// create an `InstDecoder` that supports only instructions through to `ARMv6t2` in thumb mode.
    pub fn armv6t2_thumb() -> Self {
        Self {
            mode: DecodeMode::Any,
            version: ARMVersion::v6t2,
            should_is_must: true,
            thumb: true,
        }
    }

    /// create an `InstDecoder` that supports only instructions through to `ARMv7`.
    pub fn armv7() -> Self {
        Self {
            mode: DecodeMode::Any,
            version: ARMVersion::v7,
            should_is_must: true,
            thumb: false,
        }
    }

    /// create an `InstDecoder` that supports only instructions through to `ARMv7` in thumb mode.
    pub fn armv7_thumb() -> Self {
        Self {
            mode: DecodeMode::Any,
            version: ARMVersion::v7,
            should_is_must: true,
            thumb: true,
        }
    }

    /// create an `InstDecoder` that supports only instructions through to `ARMv7ve`.
    pub fn armv7ve() -> Self {
        Self {
            mode: DecodeMode::Any,
            version: ARMVersion::v7ve,
            should_is_must: true,
            thumb: false,
        }
    }

    /// create an `InstDecoder` that supports only instructions through to `ARMv7ve` in thumb mode.
    pub fn armv7ve_thumb() -> Self {
        Self {
            mode: DecodeMode::Any,
            version: ARMVersion::v7ve,
            should_is_must: true,
            thumb: true,
        }
    }

    /// create an `InstDecoder` that supports only instructions through to `ARMv7vese`.
    pub fn armv7vese() -> Self {
        Self {
            mode: DecodeMode::Any,
            version: ARMVersion::v7vese,
            should_is_must: true,
            thumb: false,
        }
    }

    fn unpredictable(&self) -> Result<(), DecodeError> {
        if self.mode != DecodeMode::Any {
            Err(DecodeError::Unpredictable)
        } else {
            Ok(())
        }
    }
}

#[allow(non_snake_case)]
impl Decoder<ARMv7> for InstDecoder {
    #[inline]
    fn decode_into<T: Reader<<ARMv7 as Arch>::Address, <ARMv7 as Arch>::Word>>(&self, inst: &mut Instruction, words: &mut T) -> Result<(), <ARMv7 as Arch>::DecodeError> {
        inst.set_w(false);
        inst.set_wide(false);
        if self.thumb {
            return thumb::decode_into(&self, inst, words);
        } else {
            inst.set_thumb(false);
        }

        let mut word_bytes = [0u8; 4];
        words.next_n(&mut word_bytes)?;
        let word = u32::from_le_bytes(word_bytes);

        let (cond, opc_upper) = {
            let top_byte = word >> 24;
            (
                ((top_byte >> 4) & 0xf) as u8,
                ((top_byte >> 1) & 0x7) as u8
            )
        };

        if cond == 0b1111 {
            // unconditional instructions, section A5.7/page A5-214
            inst.condition = ConditionCode::AL;
            let op1 = (word >> 20) as u8;
            if op1 >= 0b1000_0000 {
                match (op1 >> 5) & 0b11 {
                    0b00 => {
                        match op1 & 0b101 {
                            0b000 |
                            0b101 => {
                                return Err(DecodeError::InvalidOpcode);
                            }
                            0b100 => {
                                // SRS (see table A5.7, op1 = 0b100xx1x0, page A5-214)
                                if !self.mode.is_any() && self.mode.is_hyp() {
                                    return Err(DecodeError::Undefined);
                                }
                                if self.should_is_must {
                                    if word & 0x000fffe0 != 0x000d0500 {
                                        return Err(DecodeError::Nonconforming);
                                    }
                                }
                                let puxw = (word >> 21) & 0b1111;
                                let P = puxw & 0b1000 != 0;
                                let U = puxw & 0b0100 != 0;
                                let W = puxw & 0b0001 != 0;
                                inst.opcode = Opcode::SRS(P, U);
                                inst.operands = [
                                    Operand::RegWBack(Reg::from_u8(13), W),
                                    Operand::Imm32(word & 0b1111),
                                    Operand::Nothing,
                                    Operand::Nothing,
                                ];
                            },
                            0b001 => {
                                // RFE (see table A5.7, op1 = 0b100xx0x1, page A5-214)
                                if !self.mode.is_any() && self.mode.is_hyp() {
                                    return Err(DecodeError::Undefined);
                                }
                                if self.should_is_must {
                                    if word & 0xffff != 0x0a00 {
                                        return Err(DecodeError::Nonconforming);
                                    }
                                }
                                let puxw = (word >> 21) & 0b1111;
                                let P = puxw & 0b1000 != 0;
                                let U = puxw & 0b0100 != 0;
                                let W = puxw & 0b0001 != 0;
                                inst.opcode = Opcode::RFE(P, U);
                                inst.operands = [
                                    Operand::RegWBack(Reg::from_u8((word >> 16) as u8 & 0b1111), W),
                                    Operand::Nothing,
                                    Operand::Nothing,
                                    Operand::Nothing,
                                ];
                            }
                            _ => {
                                unreachable!("op1 mask is 0b101 but somehow we got an invalid pattern");
                            }
                        }
                    }
                    0b01 => {
                        inst.opcode = Opcode::BLX;
                        let operand = ((word & 0xffffff) as i32) << 8 >> 7;
                        inst.operands = [
                            Operand::BranchThumbOffset(
                                operand | (
                                    ((word >> 24) & 0b1) as i32
                                )
                            ),
                            Operand::Nothing,
                            Operand::Nothing,
                            Operand::Nothing,
                        ];
                    }
                    0b10 => {
                        // op1=0b110xxxxx, see table A5-23
                        if (word >> 20) & 0b11010 == 0b00000 {
                            // the `not 11000x0{0,1}` cases in table A5-23, MCRR or MRRC
                            // but first check that bit 2 of op1 is in fact 1:
                            if (word >> 20) & 0b00100 != 0 {
                                // actually MCRR or MRRC
                                let CRm = word as u8 & 0b1111;
                                let opc1 = (word >> 4) as u8 & 0b1111;
                                let coproc = (word >> 8) as u8 & 0b1111;
                                if coproc & 0b1110 == 0b1010 {
                                    // TODO: `UNDEFINED`
                                    return Err(DecodeError::InvalidOpcode);
                                }
                                let Rt = (word >> 12) as u8 & 0b1111;
                                let Rt2 = (word >> 16) as u8 & 0b1111;
                                if Rt == 15 || Rt2 == 15 || Rt == Rt2 {
                                    // TODO: actually `UNPREDICTABLE`
                                    return Err(DecodeError::InvalidOperand);
                                }
                                if (word >> 20) & 0b00001 != 0 {
                                    inst.opcode = Opcode::MRRC(coproc, opc1, true);
                                } else {
                                    inst.opcode = Opcode::MCRR(coproc, opc1, true);
                                }
                                inst.operands = [
                                    Operand::Reg(Reg::from_u8(Rt)),
                                    Operand::Reg(Reg::from_u8(Rt2)),
                                    Operand::CReg(CReg::from_u8(CRm)),
                                    Operand::Nothing,
                                ];
                            } else {
                                return Err(DecodeError::InvalidOpcode);
                            }
                        } else {
                            // STC or LDC
                            let pudw = (word >> 21) as u8 & 0b1111;
                            let Rn = (word >> 16) as u8 & 0b1111;
                            let CRd = (word >> 12) as u8 & 0b1111;
                            let coproc = (word >> 8) as u8 & 0b1111;
                            let imm8 = word & 0b11111111;

                            if coproc & 0b1110 == 0b1010 {
                                return Err(DecodeError::InvalidOpcode);
                            }

                            if (word >> 20) & 0b00001 == 0 {
                                // op=110xxxx0, STC
                                // page A8-663

                                if pudw & 0b0010 != 0 {
                                    inst.opcode = Opcode::STCL(coproc, true);
                                } else {
                                    inst.opcode = Opcode::STC(coproc, true);
                                }
                            } else {
                                // op=110xxxx1, LDC
                                // page A8-393

                                if pudw & 0b0010 != 0 {
                                    inst.opcode = Opcode::LDCL(coproc, true);
                                } else {
                                    inst.opcode = Opcode::LDC(coproc, true);
                                }
                            }

                            let P = pudw & 0b1000 != 0;
                            let U = pudw & 0b0100 != 0;
                            let W = pudw & 0b0001 != 0;

                            inst.operands = [
                                Operand::CReg(CReg::from_u8(CRd)),
                                if P {
                                    Operand::RegDerefPreindexOffset(Reg::from_u8(Rn), (imm8 << 2) as u16, U, W)
                                } else {
                                    if W {
                                        // preindex has no wback
                                        Operand::RegDerefPostindexOffset(Reg::from_u8(Rn), (imm8 << 2) as u16, U, false)
                                    } else {
                                        Operand::RegDeref(Reg::from_u8(Rn))
                                    }
                                },
                                if !P && !W {
                                    // TODO: not sure what ldc2{l}'s <option> field really means?
                                    // at this point the invalid encoding and mrrc/mcrr forms have
                                    // been tested, so..
                                    debug_assert!(U);
                                    Operand::CoprocOption(imm8 as u8)
                                } else {
                                    Operand::Nothing
                                },
                                Operand::Nothing,
                            ];
                        }
                    }
                    0b11 => {
                        // We know the instruction looks like this...
                        // |1 1 1 1|1 1 1|x x x x|x|x x x x|x x x x|x x x x x|x x|x|x x x x|
                        //                ^ We need to check that this bit is zero, if any of the
                        //                  instructions decoded in this block are to match
                        //                  correctly.
                        // See A5-214 for the table that shows the required forms for these
                        // instructions.
                        if (op1 >> 4) & 1 != 0 {
                            return Err(DecodeError::InvalidOpcode);
                        }

                        // operands are shared between cdp2 and mcr2/mrc2, but Rt is repurposed as
                        // CRd
                        let CRm = word as u8 & 0b1111;
                        let opc2 = (word >> 5) as u8 & 0b111;
                        let coproc = (word >> 8) as u8 & 0b1111;
                        let Rt = (word >> 12) as u8 & 0b1111;
                        let CRn = (word >> 16) as u8 & 0b1111;

                        if (word >> 4) & 1 == 0 {
                            // CDP2, page A8-356
                            let opc1 = (word >> 20) as u8 & 0b1111;
                            inst.opcode = Opcode::CDP(coproc, opc1, opc2, true);
                            inst.operands = [
                                Operand::CReg(CReg::from_u8(Rt)),
                                Operand::CReg(CReg::from_u8(CRn)),
                                Operand::CReg(CReg::from_u8(CRm)),
                                Operand::Nothing,
                            ];
                        } else {
                            // MCR2/MRC2, page A8-477/A8-493
                            let opc1 = (word >> 21) as u8 & 0b111;
                            if (word >> 20) & 1 == 0 {
                                inst.opcode = Opcode::MCR(coproc, opc1, opc2, true);
                            } else {
                                inst.opcode = Opcode::MRC(coproc, opc1, opc2, true);
                            }
                            inst.operands = [
                                Operand::Reg(Reg::from_u8(Rt)),
                                Operand::CReg(CReg::from_u8(CRn)),
                                Operand::CReg(CReg::from_u8(CRm)),
                                Operand::Nothing,
                            ];
                        }
                    }
                    _ => {
                        unreachable!("op1 is two bits");
                    }
                }
            } else {
                // op1=0xxxxxxx, "Memory hints, Advanced SIMD instructions, and miscellaneous
                // instructions on pge A5-215"
                return Err(DecodeError::Incomplete);
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
                            _ => { unreachable!("mul opcode is only three bits, got: {:x}", op) }
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
                                        if Rd == 0b1110 || (Rd & 1 == 1) || Rn == 15 {
                                            return Err(DecodeError::InvalidOperand);
                                        }
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rd)),
                                            Operand::Reg(Reg::from_u8(Rd + 1)),
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
                                            Operand::Reg(Reg::from_u8(Rd)),
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
                                            Operand::Reg(Reg::from_u8(Rd)),
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
                                        unreachable!("load/store flags: {:x}", flags);
                                    }
                                }
                            }
                            0b01 => {
                    // |c o n d|0 0 0 x|x x x x x x x x x x x x x x x x|1 0 1 1|x x x x|
                    // page A5-201
                                let P = flags & 0b10000 != 0;
                                let U = flags & 0b01000 != 0;
                                let W = flags & 0b00010 != 0;

                                match flags & 0b00101 {
                                    0b00000 => {
                                        // STRHT or STRH
                                        if !P && W { // flags == 0b0x010
                                            inst.opcode = Opcode::STRHT;
                                        } else {
                                            inst.opcode = Opcode::STRH;
                                        }
                                        // According to the encoding A1 of STRH described at
                                        // A8-703, and the encoding A2 of STRHT described at
                                        // A8-705, these reserved bits must be zero.
                                        if self.should_is_must {
                                            if (word >> 8) as u8 & 0b1111 != 0 {
                                                return Err(DecodeError::Nonconforming);
                                            }
                                        }
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rd)),
                                            if P {
                                                Operand::RegDerefPreindexReg(Reg::from_u8(Rn), Reg::from_u8(LoOffset), U, W)
                                            } else {
                                                // either this is !P && W, so STRHT, and no wback,
                                                // or this is !W, and no wback
                                                Operand::RegDerefPostindexReg(Reg::from_u8(Rn), Reg::from_u8(LoOffset), U, false)
                                            },
                                            Operand::Nothing,
                                            Operand::Nothing,
                                        ];
                                    }
                                    0b00001 => {
                                        // LDRHT or LDRH
                                        if !P && W { // flags == 0b0x011
                                            inst.opcode = Opcode::LDRHT;
                                        } else {
                                            inst.opcode = Opcode::LDRH;
                                        }
                                        // According to the encoding A1 of LDRH described at
                                        // A8-447, and the encoding A2 of LDRHT described at
                                        // A8-449, these reserved bits must be zero.
                                        if self.should_is_must {
                                            if (word >> 8) as u8 & 0b1111 != 0 {
                                                return Err(DecodeError::Nonconforming);
                                            }
                                        }
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rd)),
                                            if P {
                                                Operand::RegDerefPreindexReg(Reg::from_u8(Rn), Reg::from_u8(LoOffset), U, W)
                                            } else {
                                                // either this is !P && W, so LDRHT, and no wback,
                                                // or this is !W, and no wback
                                                Operand::RegDerefPostindexReg(Reg::from_u8(Rn), Reg::from_u8(LoOffset), U, false)
                                            },
                                            Operand::Nothing,
                                            Operand::Nothing,
                                        ];
                                    }
                                    0b00100 => {
                                        // STRHT or STRH (immediate)
                                        if !P && W { // flags == 0b0x110
                                            inst.opcode = Opcode::STRHT;
                                        } else {
                                            inst.opcode = Opcode::STRH;
                                        }
                                        let imm = (HiOffset << 4) as u16 | LoOffset as u16;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rd)),
                                            if P {
                                                Operand::RegDerefPreindexOffset(Reg::from_u8(Rn), imm, U, W)
                                            } else {
                                                // either this is !P && W, so STRHT, and no wback,
                                                // or this is !W, and no wback
                                                Operand::RegDerefPostindexOffset(Reg::from_u8(Rn), imm, U, false)
                                            },
                                            Operand::Nothing,
                                            Operand::Nothing,
                                        ];
                                    }
                                    0b00101 => {
                                        // LDRHT or LDRH (immediate)
                                        if !P && W { // flags == 0b0x111
                                            inst.opcode = Opcode::LDRHT;
                                        } else {
                                            inst.opcode = Opcode::LDRH;
                                        }
                                        let imm = (HiOffset << 4) as u16 | LoOffset as u16;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rd)),
                                            if P {
                                                Operand::RegDerefPreindexOffset(Reg::from_u8(Rn), imm, U, W)
                                            } else {
                                                // either this is !P && W, so LDRHT, and no wback,
                                                // or this is !W, and no wback
                                                Operand::RegDerefPostindexOffset(Reg::from_u8(Rn), imm, U, false)
                                            },
                                            Operand::Nothing,
                                            Operand::Nothing,
                                        ];
                                    }
                                    o => {
                                        unreachable!("all of op2=01 in table A5-10 should be handled, got unexpected pattern {:b}", o);
                                    }
                                }
                                return Ok(());
                            }
                            0b10 => {
                    // |c o n d|0 0 0 x|x x x x x x x x x x x x x x x x|1 1 0 1|x x x x|
                    // page A5-201
                                let P = flags & 0b10000 != 0;
                                let U = flags & 0b01000 != 0;
                                let W = flags & 0b00010 != 0;

                                match flags & 0b00101 {
                                    0b00000 => {
                                        // LDRD or invalid
                                        if !P && W { // flags == 0b0x010
                                            return Err(DecodeError::InvalidOperand);
                                        } else {
                                            inst.opcode = Opcode::LDRD;
                                        }
                                        if self.should_is_must {
                                            // According to encoding A1 of LDRD described in
                                            // A8-431, these bits should be zero.
                                            if (word >> 8) & 0b1111 != 0 {
                                                return Err(DecodeError::Nonconforming);
                                            }
                                        }
                                        let Rm = word as u8 & 0b1111;
                                        let Rt = (word >> 12) as u8 & 0b1111;
                                        if Rt & 1 != 0 {
                                            return Err(DecodeError::InvalidOperand);
                                        }
                                        if Rt == 15 {
                                            return Err(DecodeError::InvalidOperand);
                                        }
                                        let Rn = (word >> 16) as u8 & 0b1111;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rt)),
                                            Operand::Reg(Reg::from_u8(Rt + 1)),
                                            if P {
                                                Operand::RegDerefPreindexReg(Reg::from_u8(Rn), Reg::from_u8(Rm), U, W)
                                            } else {
                                                // either !P & W (invalid) or !W
                                                Operand::RegDerefPostindexReg(Reg::from_u8(Rn), Reg::from_u8(Rm), U, false)
                                            },
                                            Operand::Nothing,
                                        ];
                                    },
                                    0b00001 => {
                                        // LDRSB or LDRSBT
                                        if !P && W { // flags == 0b0x010
                                            inst.opcode = Opcode::LDRSBT;
                                        } else {
                                            inst.opcode = Opcode::LDRSB;
                                        }
                                        if self.should_is_must {
                                            // According to the A1 encoding of LDRSB described in
                                            // A8-455, and the A2 encoding of LDRSBT described in
                                            // A8-457, these reserved bits should be zero.
                                            if (word >> 8) & 0b1111 != 0 {
                                                return Err(DecodeError::Nonconforming);
                                            }
                                        }
                                        let Rm = word as u8 & 0b1111;
                                        let Rt = (word >> 12) as u8 & 0b1111;
                                        let Rn = (word >> 16) as u8 & 0b1111;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rt)),
                                            if P {
                                                Operand::RegDerefPreindexReg(Reg::from_u8(Rn), Reg::from_u8(Rm), U, W)
                                            } else {
                                                // either !P & W (ldrsbt) or !W
                                                Operand::RegDerefPostindexReg(Reg::from_u8(Rn), Reg::from_u8(Rm), U, false)
                                            },
                                            Operand::Nothing,
                                            Operand::Nothing,
                                        ];
                                    },
                                    0b00100 => {
                                        // LDRD (immediate)
                                        if !P && W { // flags == 0b0x110
                                            return Err(DecodeError::InvalidOperand);
                                        } else {
                                            inst.opcode = Opcode::LDRD;
                                        }
                                        let Rt = (word >> 12) as u8 & 0b1111;
                                        if Rt & 1 != 0 {
                                            return Err(DecodeError::InvalidOperand);
                                        }
                                        if Rt == 14 || Rn == 15 {
                                            return Err(DecodeError::InvalidOperand);
                                        }
                                        let Rn = (word >> 16) as u8 & 0b1111;
                                        let imm = (HiOffset << 4) as u16 | LoOffset as u16;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rt)),
                                            Operand::Reg(Reg::from_u8(Rt + 1)),
                                            if P {
                                                Operand::RegDerefPreindexOffset(Reg::from_u8(Rn), imm, U, W)
                                            } else {
                                                // either !P & W (invalid) or !W
                                                Operand::RegDerefPostindexOffset(Reg::from_u8(Rn), imm, U, false)
                                            },
                                            Operand::Nothing,
                                        ];
                                    },
                                    0b00101 => {
                                        // LDRSB or LDRSBT (immediate)
                                        if !P && W { // flags == 0b0x010
                                            inst.opcode = Opcode::LDRSBT;
                                        } else {
                                            inst.opcode = Opcode::LDRSB;
                                        }
                                        let Rt = (word >> 12) as u8 & 0b1111;
                                        let Rn = (word >> 16) as u8 & 0b1111;
                                        let imm = (HiOffset << 4) as u16 | LoOffset as u16;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rt)),
                                            if P {
                                                Operand::RegDerefPreindexOffset(Reg::from_u8(Rn), imm, U, W)
                                            } else {
                                                // either !P & W (ldrsbt) or !W
                                                Operand::RegDerefPostindexOffset(Reg::from_u8(Rn), imm, U, false)
                                            },
                                            Operand::Nothing,
                                            Operand::Nothing,
                                        ];
                                    },
                                    _ => { unreachable!("impossible bit pattern"); }
                                }
                            }
                            0b11 => {
                    // |c o n d|0 0 0 x|x x x x x x x x x x x x x x x x|1 1 1 1|x x x x|
                    // page A5-201
                                let P = flags & 0b10000 != 0;
                                let U = flags & 0b01000 != 0;
                                let W = flags & 0b00010 != 0;

                                match flags & 0b00101 {
                                    0b00000 => {
                                        // STRD or invalid
                                        if !P && W { // flags == 0b0x010
                                            return Err(DecodeError::InvalidOperand);
                                        } else {
                                            inst.opcode = Opcode::STRD;
                                        }

                                        if self.should_is_must {
                                            // According to encoding A1 of STRD described at
                                            // A8-689, these reserved bits should be zero.
                                            if (word >> 8) & 0b1111 != 0 {
                                                return Err(DecodeError::Nonconforming);
                                            }
                                        }
                                        let Rm = word as u8 & 0b1111;
                                        let Rt = (word >> 12) as u8 & 0b1111;
                                        if Rt & 1 != 0 {
                                            return Err(DecodeError::InvalidOperand);
                                        }
                                        let Rn = (word >> 16) as u8 & 0b1111;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rt)),
                                            Operand::Reg(Reg::from_u8(Rt + 1)),
                                            if P {
                                                Operand::RegDerefPreindexReg(Reg::from_u8(Rn), Reg::from_u8(Rm), U, W)
                                            } else {
                                                // either !P & W (invalid) or !W
                                                Operand::RegDerefPostindexReg(Reg::from_u8(Rn), Reg::from_u8(Rm), U, false)
                                            },
                                            Operand::Nothing,
                                        ];
                                    },
                                    0b00001 => {
                                        // LDRSH or LDRSHT
                                        if !P && W { // flags == 0b0x010
                                            inst.opcode = Opcode::LDRSHT;
                                        } else {
                                            inst.opcode = Opcode::LDRSH;
                                        }
                                        if self.should_is_must {
                                            // According to encoding A1 of LDRSH described at
                                            // A8-463, and encoding A2 of LDRSHT described at
                                            // A8-465, these reserved bits should be zero.
                                            if (word >> 8) & 0b1111 != 0 {
                                                return Err(DecodeError::Nonconforming);
                                            }
                                        }
                                        let Rm = word as u8 & 0b1111;
                                        let Rt = (word >> 12) as u8 & 0b1111;
                                        let Rn = (word >> 16) as u8 & 0b1111;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rt)),
                                            if P {
                                                Operand::RegDerefPreindexReg(Reg::from_u8(Rn), Reg::from_u8(Rm), U, W)
                                            } else {
                                                // either !P & W (ldrsht) or !W
                                                Operand::RegDerefPostindexReg(Reg::from_u8(Rn), Reg::from_u8(Rm), U, false)
                                            },
                                            Operand::Nothing,
                                            Operand::Nothing,
                                        ];
                                    },
                                    0b00100 => {
                                        // STRD (immediate)
                                        if !P && W { // flags == 0b0x110
                                            return Err(DecodeError::InvalidOperand);
                                        } else {
                                            inst.opcode = Opcode::STRD;
                                        }
                                        let Rt = (word >> 12) as u8 & 0b1111;
                                        if Rt & 1 != 0 {
                                            return Err(DecodeError::InvalidOperand);
                                        }
                                        if Rt == 15 {
                                            return Err(DecodeError::InvalidOperand);
                                        }
                                        let Rn = (word >> 16) as u8 & 0b1111;
                                        let imm = (HiOffset << 4) as u16 | LoOffset as u16;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rt)),
                                            Operand::Reg(Reg::from_u8(Rt + 1)),
                                            if P {
                                                Operand::RegDerefPreindexOffset(Reg::from_u8(Rn), imm, U, W)
                                            } else {
                                                // either !P & W (invalid) or !W
                                                Operand::RegDerefPostindexOffset(Reg::from_u8(Rn), imm, U, false)
                                            },
                                            Operand::Nothing,
                                        ];
                                    },
                                    0b00101 => {
                                        // LDRSH or LDRSHT (immediate)
                                        if !P && W { // flags == 0b0x010
                                            inst.opcode = Opcode::LDRSHT;
                                        } else {
                                            inst.opcode = Opcode::LDRSH;
                                        }
                                        let Rt = (word >> 12) as u8 & 0b1111;
                                        let Rn = (word >> 16) as u8 & 0b1111;
                                        let imm = (HiOffset << 4) as u16 | LoOffset as u16;
                                        inst.operands = [
                                            Operand::Reg(Reg::from_u8(Rt)),
                                            if P {
                                                Operand::RegDerefPreindexOffset(Reg::from_u8(Rn), imm, U, W)
                                            } else {
                                                // either !P & W (ldrsht) or !W
                                                Operand::RegDerefPostindexOffset(Reg::from_u8(Rn), imm, U, false)
                                            },
                                            Operand::Nothing,
                                            Operand::Nothing,
                                        ];
                                    },
                                    _ => { unreachable!("impossible bit pattern"); }
                                }
                            }
                            _ => { unreachable!("op is two bits"); }
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
                                    // test B bit (bit 9)
                                    if word & 0b10_0000_0000 != 0 {
                                        // TODO: ARMv7VE flag
                                        let SYSm = (((word >> 9) & 1) << 4) as u8 | ((word >> 16) & 0x0f) as u8;
                                        let R = (word >> 22) & 1;

                                        if opcode & 0b01 == 0b01 {
                                            if self.should_is_must {
                                                if word & 0b1111_1100_0000_0000 != 0xf000 {
                                                    return Err(DecodeError::InvalidOperand);
                                                }
                                            }
                                            inst.opcode = Opcode::MSR;
                                            inst.operands[0] = if let Some(reg) = Reg::from_sysm(R != 0, SYSm) {
                                                reg
                                            } else {
                                                return Err(DecodeError::InvalidOperand);
                                            };
                                            inst.operands[1] = Operand::Reg(Reg::from_u8(word as u8 & 0b1111));
                                            inst.operands[2] = Operand::Nothing;
                                            inst.operands[3] = Operand::Nothing;
                                        } else {
                                            if self.should_is_must {
                                                if word & 0b0000_1100_0000_1111 != 0x0000 {
                                                    return Err(DecodeError::InvalidOperand);
                                                }
                                            }
                                            inst.opcode = Opcode::MRS;
                                            inst.operands[0] = Operand::Reg(Reg::from_u8((word >> 12) as u8 & 0b1111));
                                            inst.operands[1] = if let Some(reg) = Reg::from_sysm(R != 0, SYSm) {
                                                reg
                                            } else {
                                                return Err(DecodeError::InvalidOperand);
                                            };
                                            inst.operands[2] = Operand::Nothing;
                                            inst.operands[3] = Operand::Nothing;
                                        }
                                    } else {
                                        match opcode & 0b11 {
                                            0b00 |
                                            0b10 => {
                                                inst.opcode = Opcode::MRS;
                                                let src = if self.mode.is_system() {
                                                    let R = (word >> 22) & 1 != 0;
                                                    if R {
                                                        Operand::SPSR
                                                    } else {
                                                        Operand::CPSR
                                                    }
                                                } else {
                                                    Operand::APSR
                                                };
                                                inst.operands[0] = Operand::Reg(Reg::from_u8((word >> 12) as u8 & 0b1111));
                                                inst.operands[1] = src;
                                                inst.operands[2] = Operand::Nothing;
                                                inst.operands[3] = Operand::Nothing;
                                            }
                                            0b01 => {
                                                inst.opcode = Opcode::MSR;
                                                let mask = (word >> 16) & 0b1111;
                                                if mask & 0b11 == 0 {
                                                    if self.mode.is_user() {
                                                        inst.operands[0] = Operand::StatusRegMask(StatusRegMask::from_raw(mask as u8)?);
                                                        inst.operands[1] = Operand::Reg(Reg::from_u8(word as u8 & 0b1111));
                                                        inst.operands[2] = Operand::Nothing;
                                                        inst.operands[3] = Operand::Nothing;
                                                    } else {
                                                        // MSR with op == 01, op == xx00, but not
                                                        // user mode
                                                        return Err(DecodeError::InvalidOperand);
                                                    }
                                                } else {
                                                    if self.mode.is_system() {
                                                        // bit 22 is the high bit of opcode, so..
                                                        let R = (word >> 22) as u8 & 1;
                                                        inst.operands[0] = Operand::StatusRegMask(StatusRegMask::from_raw((R << 4) | mask as u8)?);
                                                        inst.operands[1] = Operand::Reg(Reg::from_u8(word as u8 & 0b1111));
                                                        inst.operands[2] = Operand::Nothing;
                                                        inst.operands[3] = Operand::Nothing;
                                                    } else {
                                                        // MSR with op == 01, op != xx00
                                                        return Err(DecodeError::InvalidOperand);
                                                    }
                                                }
                                            },
                                            0b11 => {
                                                if !self.mode.is_system() {
                                                    return Err(DecodeError::InvalidOperand);
                                                }

                                                inst.opcode = Opcode::MSR;
                                                let mask = (word >> 16) & 0b1111;
                                                // bit 22 is the high bit of opcode, so..
                                                let R = (word >> 22) & 1;
                                                inst.operands[0] = Operand::StatusRegMask(StatusRegMask::from_raw((R << 4) as u8 | mask as u8)?);
                                                inst.operands[1] = Operand::Reg(Reg::from_u8(word as u8 & 0b1111));
                                                inst.operands[2] = Operand::Nothing;
                                                inst.operands[3] = Operand::Nothing;
                                            }
                                            _ => {
                                                unreachable!("opcode is masked to two bits here");
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
                                    match (word >> 21) & 0b11 {
                                        0b00 => {
                                            inst.opcode = Opcode::QADD;
                                        },
                                        0b01 => {
                                            inst.opcode = Opcode::QSUB;
                                        },
                                        0b10 => {
                                            inst.opcode = Opcode::QDADD;
                                        },
                                        0b11 => {
                                            inst.opcode = Opcode::QDSUB;
                                        },
                                        _ => {
                                            unreachable!("bit pattern masked by 0b11 but large value observed");
                                        }
                                    }

                                    if self.should_is_must {
                                        if (word >> 8) & 0b1111 != 0 {
                                            return Err(DecodeError::Nonconforming);
                                        }
                                    }

                                    inst.operands = [
                                        Operand::Reg(Reg::from_u8(((word >> 12) & 0b1111) as u8)),
                                        Operand::Reg(Reg::from_u8((word & 0b1111) as u8)),
                                        Operand::Reg(Reg::from_u8(((word >> 16) & 0b1111) as u8)),
                                        Operand::Nothing
                                    ];
                                }
                                0b110 => {
                                    if (word >> 21) & 0b11 != 0b11 {
                                        return Err(DecodeError::InvalidOpcode);
                                    }

                                    // "ERET" page B9-1968, from A5.2.12, page A5-205
                                    if self.should_is_must {
                                        if word & 0b1111_1111_1111_1111 != 0b0000_0000_0000_0110_1110 {
                                            return Err(DecodeError::Nonconforming);
                                        }
                                    }
                                    inst.opcode = Opcode::ERET;
                                    inst.operands = [
                                        Operand::Nothing,
                                        Operand::Nothing,
                                        Operand::Nothing,
                                        Operand::Nothing,
                                    ];
                                },
                                0b111 => {
                                    // "BKPT, HVC, SMC" from table A5-14/page A5-205
                                    match (word >> 21) & 0b11 {
                                        0b00 => {
                                            return Err(DecodeError::InvalidOpcode);
                                        }
                                        0b01 => {
                                            // BKPT
                                            if self.should_is_must {
                                                if (word >> 28) & 0b1111 != 0b1110 {
                                                    // "BKPT must be encoded with AL condition"
                                                    return Err(DecodeError::InvalidOpcode);
                                                }
                                            }
                                            inst.opcode = Opcode::BKPT;
                                            let immlo = word & 0x0f;
                                            let imm = ((word >> 4) & 0xfff0) | immlo;
                                            inst.operands = [
                                                Operand::Imm32(imm),
                                                Operand::Nothing,
                                                Operand::Nothing,
                                                Operand::Nothing,
                                            ];
                                        }
                                        0b10 => {
                                            // HVC
                                            if self.should_is_must {
                                                if (word >> 28) & 0b1111 != 0b1110 {
                                                    // "HVC must be encoded with AL condition"
                                                    return Err(DecodeError::InvalidOpcode);
                                                }
                                            }
                                            inst.opcode = Opcode::HVC;
                                            let immlo = word & 0x0f;
                                            let imm = ((word >> 4) & 0xfff0) | immlo;
                                            inst.operands = [
                                                Operand::Imm32(imm),
                                                Operand::Nothing,
                                                Operand::Nothing,
                                                Operand::Nothing,
                                            ];
                                        }
                                        0b11 => {
                                            // SMC
                                            if self.should_is_must {
                                                if word & 0xf_ff_ff_70 == 0x1_60_00_70 {
                                                    // "SMC must be encoded with AL condition"
                                                    return Err(DecodeError::InvalidOpcode);
                                                }
                                            }
                                            inst.opcode = Opcode::SMC;
                                            let immlo = word & 0x0f;
                                            let imm = ((word >> 4) & 0xfff0) | immlo;
                                            inst.operands = [
                                                Operand::Imm32(imm),
                                                Operand::Nothing,
                                                Operand::Nothing,
                                                Operand::Nothing,
                                            ];
                                        }
                                        _ => { unreachable!("impossible bit pattern"); }
                                    }
                                },
                                _ => {
                                    unreachable!("op2 is a three bit field, got an invalid pattern");
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
                                    unreachable!("word masked to two bits");
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

                        // |c o n d|0 0 0|x x x x|0|x x x x|x x x x|x x x x x|x x|x|x x x x|
                        // interpret the operands as
                        // | Rn | Rd | shift info... |
                        //
                        // note that bits 7 down to 4 are either `x . . 0` or `0 x x 1`, though.
                        // those bits comprise `op2` and are handled when determining where in
                        // table A5-2 this instruction lies.

                        let (Rn, Rd, shift_spec, Rm) = {
                            let Rm = (word & 0x0f) as u8;
                            let shift_spec = (word & 0xfff) as u16;
                            let word = word >> 12;
                            let Rd = (word & 0x0f) as u8;
                            let Rn = ((word >> 4) & 0x0f) as u8;
                            (Rn, Rd, shift_spec, Rm)
                        };

                        let reg_shift = RegShift::from_raw(shift_spec);
                        let last_operand = if reg_shift.is_noop() {
                            // no shift, so the operand is just a register.
                            //
                            // TODO: this shift style is `lsl 0`, and not incorrect to report
                            // as just that. should it be impossible for `format_reg_shift` to
                            // get a register shifted by lsl 0? simplifying the register here
                            // seems valuable for consumers of individual operands. as-is, this
                            // is inconsistent across the library, which is probably the worst
                            // it could be...
                            Operand::Reg(Reg::from_u8(Rm))
                        } else {
                            Operand::RegShift(reg_shift)
                        };

                        match inst.opcode {
                            Opcode::MOV | Opcode::MVN => {
                                if self.should_is_must {
                                    if Rn != 0 {
                                        return Err(DecodeError::Nonconforming);
                                    }
                                }
                                inst.operands = [
                                    Operand::Reg(Reg::from_u8(Rd)),
                                    last_operand,
                                    Operand::Nothing,
                                    Operand::Nothing
                                ];
                            }

                            Opcode::CMP | Opcode::CMN => {
                                if self.should_is_must {
                                    if Rd != 0 {
                                        return Err(DecodeError::Nonconforming);
                                    }
                                }
                                inst.operands = [
                                    Operand::Reg(Reg::from_u8(Rn)),
                                    last_operand,
                                    Operand::Nothing,
                                    Operand::Nothing
                                ];
                            }

                            _ => {
                                inst.operands = [
                                    Operand::Reg(Reg::from_u8(Rd)),
                                    Operand::Reg(Reg::from_u8(Rn)),
                                    last_operand,
                                    Operand::Nothing
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
                    match opcode & 0b0011 {
                        0b00 => {
                            // 16-bit immediate load, MOV (immediate) on page A8-485
                            inst.opcode = Opcode::MOV;
                            inst.operands = [
                                Operand::Reg(Reg::from_u8(((word >> 12) & 0b1111) as u8)),
                                Operand::Imm32(((word >> 4) & 0xf000) | (word & 0xfff)),
                                Operand::Nothing,
                                Operand::Nothing,
                            ];
                        }
                        0b10 => {
                            // High halfword 16-bit immediate load, MOVT on page A8-492
                            inst.opcode = Opcode::MOVT;
                            inst.operands = [
                                Operand::Reg(Reg::from_u8(((word >> 12) & 0b1111) as u8)),
                                Operand::Imm32(((word >> 4) & 0xf000) | (word & 0xfff)),
                                Operand::Nothing,
                                Operand::Nothing,
                            ];
                        }
                        0b01 => {
                            // MSR (immediate), and hints on page A5-204, op==0
                            let op1 = (word >> 16) & 0b1111;
                            match op1 {
                                0b0000 => {

                                },
                                _ => {
                                    // Move to Special register, Application level MSR (immediate) on
                                    // page A8-499
                                    if self.should_is_must {
                                        if (word >> 12) & 0b1111 != 0b1111 {
                                            return Err(DecodeError::Nonconforming);
                                        }
                                    }
                                    inst.operands = [
                                        Operand::StatusRegMask(StatusRegMask::from_raw(op1 as u8)?),
                                        Operand::Imm32(word & 0xfff),
                                        Operand::Nothing,
                                        Operand::Nothing,
                                    ];
                                    inst.opcode = Opcode::MSR;
                                },
                            }
                        }
                        0b11 => {
                            // MSR (immediate), and hints on page A5-204, op==1
                            if self.should_is_must {
                                if (word >> 12) & 0b1111 != 0b1111 {
                                    return Err(DecodeError::Nonconforming);
                                }
                            }
                            inst.operands = [
                                Operand::StatusRegMask(StatusRegMask::from_raw((word >> 16) as u8 & 0b1111 | 0b10000)?),
                                Operand::Imm32(word & 0xfff),
                                Operand::Nothing,
                                Operand::Nothing,
                            ];
                            inst.opcode = Opcode::MSR;
                        }
                        _ => { unreachable!("impossible bit pattern"); }
                    }
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
                        let imm = word & 0x000000ff;
                        let imm = (imm as u32).rotate_right(2 * (rot >> 8));
                        ((word >> 16) as u8 & 0x0f, (word >> 12) as u8 & 0x0f, imm)
                    };
                    if (opcode == 0b0010 || opcode == 0b0100) && Rn == 0b1111 {
                        inst.opcode = Opcode::ADR;
                    }
                    match opcode {
                        // CMP/CMN (immediate)
                        0b1010 | 0b1011 => {
                            // According to A8-368, there are 4 bits right above the immediate that
                            // are reserved and should be zero
                            if self.should_is_must && (word >> 12) as u8 & 0b1111 != 0 {
                                return Err(DecodeError::Nonconforming);
                            }
                            // compare has no destination register, only a source.
                            inst.operands = [
                                Operand::Reg(Reg::from_u8(Rn)),
                                Operand::Imm32(imm),
                                Operand::Nothing,
                                Operand::Nothing,
                            ];
                        }
                        // MOV (immediate)
                        0b1101 => {
                            // mov has no source *register*, only the immediate being moved.
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
                        0b010 => Opcode::STRT,
                        0b011 => Opcode::LDRT,
                        0b110 => Opcode::STRBT,
                        0b111 => Opcode::LDRBT,
                        _ => { unreachable!(); }
                    };
                    inst.operands = [
                        Operand::Reg(Reg::from_u8(Rt)),
                        Operand::RegDerefPostindexOffset(Reg::from_u8(Rn), imm as u16, add, false),
                        Operand::Nothing,
                        Operand::Nothing,
                    ];
                } else {
                    /*
                    xx0x0 not 0x010 -> STR (imm)
                    xx0x1 not 0x011 -> LDR (imm)
                    xx1x0 not 0x110 -> STRB (imm)
                    xx1x1 not 0x111 -> LDRB (imm)
                    */
                    let P = (op & 0b10000) != 0;
                    let W = (op & 0b00010) != 0;
                    let op = op & 0b00101;
                    inst.opcode = if !P && W {
                        // Table A5-15
                        // strt, ldrt, strbt, ldrbt
                        match op {
                            0b000 => Opcode::STRT,
                            0b001 => Opcode::LDRT,
                            0b100 => Opcode::STRBT,
                            0b101 => Opcode::LDRBT,
                            _ => { unreachable!("bad bit pattern, table A5-15"); }
                        }
                    } else {
                        match op {
                            0b000 => Opcode::STR,
                            0b001 => {
                                if Rn == 0b1111 {
                                    inst.operands = [
                                        Operand::Reg(Reg::from_u8(Rt)),
                                        if P {
                                            Operand::RegDerefPreindexOffset(Reg::from_u8(Rn), imm as u16, add, W)
                                        } else {
                                            Operand::RegDerefPostindexOffset(Reg::from_u8(Rn), imm as u16, add, W)
                                        },
                                        Operand::Nothing,
                                        Operand::Nothing,
                                    ];
                                    inst.opcode = Opcode::LDR;
                                    return Ok(());
                                }
                                Opcode::LDR
                            },
                            0b100 => Opcode::STRB,
                            0b101 => {
                                if Rn == 0b1111 {
                                    inst.operands = [
                                        Operand::Reg(Reg::from_u8(Rt)),
                                        if P {
                                            Operand::RegDerefPreindexOffset(Reg::from_u8(Rn), imm as u16, add, W)
                                        } else {
                                            Operand::RegDerefPostindexOffset(Reg::from_u8(Rn), imm as u16, add, W)
                                        },
                                        Operand::Nothing,
                                        Operand::Nothing,
                                    ];
                                    inst.opcode = Opcode::LDRB;
                                    return Ok(());
                                }
                                Opcode::LDRB
                            },
                            _ => { unreachable!(); }
                        }
                    };
                    inst.operands = [
                        Operand::Reg(Reg::from_u8(Rt)),
                        if P {
                            Operand::RegDerefPreindexOffset(Reg::from_u8(Rn), imm as u16, add, W)
                        } else {
                            Operand::RegDerefPostindexOffset(Reg::from_u8(Rn), imm as u16, add, W)
                        },
                        Operand::Nothing,
                        Operand::Nothing,
                    ];
                }
            },
            0b011 => {
                // page A5-192 to distinguish the following:
                // check for media instructions, and if not, load/store word and unsigned byte
                if (word & 0x00000010) != 0 {
                // |c o n d|0 1 1|x x x x|x|x x x x|x x x x|x x x x x|x x|1|x x x x|
                    // using language from A5-206: A == 1 and B == 1
                    // so this is media instructions (A5-207)
                    return Err(DecodeError::Incomplete);
                } else {
                // |c o n d|0 1 1|x x x x|x|x x x x|x x x x|x x x x x|x x|0|x x x x|
                    // instructions here are A == 1, B == 0 in A5-206
                    let op = ((word >> 20) & 0x1f) as u8;

                    let P = (op & 0b10000) != 0;
                    let U = (op & 0b01000) != 0;
                    let W = (op & 0b00010) != 0;
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
                            0b010 => Opcode::STRT,
                            0b011 => Opcode::LDRT,
                            0b110 => Opcode::STRBT,
                            0b111 => Opcode::LDRBT,
                            _ => { unreachable!(); }
                        };
                    } else {
                        /*
                        xx0x0 not 0x010 -> STR (imm)
                        xx0x1 not 0x011 -> LDR (imm)
                        xx1x0 not 0x110 -> STRB (imm)
                        xx1x1 not 0x111 -> LDRB (imm)
                        */
                        let op = op & 0b00101;
                        inst.opcode = match op {
                            0b000 => Opcode::STR,
                            0b001 => Opcode::LDR,
                            0b100 => Opcode::STRB,
                            0b101 => Opcode::LDRB,
                            _ => { unreachable!(); }
                        };
                    }
                    let (Rt, shift) = {
                        let shift = (word & 0xfff) as u16;
                        let word = word >> 12;
                        let Rt = (word & 0xf) as u8;
                        (Rt, shift)
                    };
                    let Rn = (word >> 16) as u8 & 0b1111;
                    inst.operands = [
                        Operand::Reg(Reg::from_u8(Rt)),
                        if P {
                            Operand::RegDerefPreindexRegShift(Reg::from_u8(Rn), RegShift::from_raw(shift), U, W)
                        } else {
                            Operand::RegDerefPostindexRegShift(Reg::from_u8(Rn), RegShift::from_raw(shift), U, false)
                        },
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
                        Opcode::STM(add, pre, false, usermode)
                    } else {
                        Opcode::LDM(add, pre, false, usermode)
                    };
                    inst.operands = [
                        Operand::RegWBack(Reg::from_u8(((word >> 16) & 0xf) as u8), wback),
                        Operand::RegList((word & 0xffff) as u16),
                        Operand::Nothing,
                        Operand::Nothing,
                    ];
                } else if op < 0b110000 {
                    // 10xxxx
                    inst.opcode = Opcode::B;

                    // the + 2 is to compensate for an architecturally-defined initial offset
                    let imm24 = ((((word & 0x00ff_ffff) + 2) << 8) as i32) >> 8;

                    inst.operands = [
                        Operand::BranchOffset(imm24),
                        Operand::Nothing,
                        Operand::Nothing,
                        Operand::Nothing,
                    ];
                } else {
                    // 11xxxx

                    // the + 2 is to compensate for an architecturally-defined initial offset
                    let imm24 = ((((word & 0x00ff_ffff) + 2) << 8) as i32) >> 8;

                    inst.opcode = Opcode::BL;
                    inst.operands = [
                        Operand::BranchOffset(imm24),
                        Operand::Nothing,
                        Operand::Nothing,
                        Operand::Nothing,
                    ];
                }
            },
            0b110 => {
                // coprocessor instructions and supervisor call
                // page A5-213
                // low bit of 0b110 or 0b111 corresponds to high bit of op1
                //
                // op1=0b110xxxxx, see table A5-23
                let coproc = (word >> 8) as u8 & 0b1111;

                if coproc & 0b1110 == 0b1010 {
                    // Advanced SIMD, Floating-point, op1 = 0xxxxx
                    return Err(DecodeError::Incomplete);
                }

                if (word >> 20) & 0b11010 == 0b00000 {
                    // the `not 11000x0{0,1}` cases in table A5-23, MCRR or MRRC
                    // but first check that bit 2 of op1 is in fact 1:
                    if (word >> 20) & 0b00100 != 0 {
                        // actually MCRR or MRRC
                        let CRm = word as u8 & 0b1111;
                        let opc1 = (word >> 4) as u8 & 0b1111;
                        let Rt = (word >> 12) as u8 & 0b1111;
                        let Rt2 = (word >> 16) as u8 & 0b1111;
                        if Rt == 15 || Rt2 == 15 || Rt == Rt2 {
                            // TODO: actually `UNPREDICTABLE`
                            return Err(DecodeError::InvalidOperand);
                        }
                        if (word >> 20) & 0b00001 != 0 {
                            inst.opcode = Opcode::MRRC(coproc, opc1, false);
                        } else {
                            inst.opcode = Opcode::MCRR(coproc, opc1, false);
                        }
                        inst.operands = [
                            Operand::Reg(Reg::from_u8(Rt)),
                            Operand::Reg(Reg::from_u8(Rt2)),
                            Operand::CReg(CReg::from_u8(CRm)),
                            Operand::Nothing,
                        ];
                    } else {
                        return Err(DecodeError::InvalidOpcode);
                    }
                } else {
                    // STC or LDC
                    let pudw = (word >> 21) as u8 & 0b1111;
                    let Rn = (word >> 16) as u8 & 0b1111;
                    let CRd = (word >> 12) as u8 & 0b1111;
                    let imm8 = word & 0b11111111;

                    if (word >> 20) & 0b00001 == 0 {
                        // op=110xxxx0, STC
                        // page A8-663

                        if pudw & 0b0010 != 0 {
                            inst.opcode = Opcode::STCL(coproc, false);
                        } else {
                            inst.opcode = Opcode::STC(coproc, false);
                        }
                    } else {
                        // op=110xxxx1, LDC
                        // page A8-393

                        if pudw & 0b0010 != 0 {
                            inst.opcode = Opcode::LDCL(coproc, false);
                        } else {
                            inst.opcode = Opcode::LDC(coproc, false);
                        }
                    }

                    let P = pudw & 0b1000 != 0;
                    let U = pudw & 0b0100 != 0;
                    let W = pudw & 0b0001 != 0;

                    inst.operands = [
                        Operand::CReg(CReg::from_u8(CRd)),
                        if P {
                            Operand::RegDerefPreindexOffset(Reg::from_u8(Rn), (imm8 << 2) as u16, U, W)
                        } else {
                            if W {
                                // postindex always has wback
                                Operand::RegDerefPostindexOffset(Reg::from_u8(Rn), (imm8 << 2) as u16, U, true)
                            } else {
                                Operand::RegDeref(Reg::from_u8(Rn))
                            }
                        },
                        if !P && !W {
                            // TODO: not sure what ldc2{l}'s <option> field really means?
                            // at this point the invalid encoding and mrrc/mcrr forms have
                            // been tested, so..
                            debug_assert!(U);
                            Operand::CoprocOption(imm8 as u8)
                        } else {
                            Operand::Nothing
                        },
                        Operand::Nothing,
                    ];
                }
            },
            0b111 => {
                // coprocessor instructions and supervisor call
                // page A5-213
                // low bit of 0b110 or 0b111 corresponds to high bit of op1
                //
                // op1=0b111xxxxx, see table A5-22
                let op1 = (word >> 20) & 0b111111;
                if ((op1 >> 4) & 1) != 0 {
                    inst.opcode = Opcode::SVC;
                    let imm = word & 0xff_ff_ff;
                    inst.operands = [
                        Operand::Imm32(imm),
                        Operand::Nothing,
                        Operand::Nothing,
                        Operand::Nothing,
                    ];
                    return Ok(());
                }

                let coproc = (word >> 8) as u8 & 0b1111;

                if coproc & 0b1110 == 0b1010 {
                    // Advanced SIMD, Floating-point, op1 = 0xxxxx
                    return Err(DecodeError::Incomplete);
                }

                if (word >> 4) & 1 == 0 {
                    // CDP, page A8-356
                    let CRm = word as u8 & 0b1111;
                    let opc2 = (word >> 5) as u8 & 0b111;
                    let Rt = (word >> 12) as u8 & 0b1111;
                    let CRn = (word >> 16) as u8 & 0b1111;

                    let opc1 = (word >> 20) as u8 & 0b1111;
                    inst.opcode = Opcode::CDP(coproc, opc1, opc2, false);
                    inst.operands = [
                        Operand::CReg(CReg::from_u8(Rt)),
                        Operand::CReg(CReg::from_u8(CRn)),
                        Operand::CReg(CReg::from_u8(CRm)),
                        Operand::Nothing,
                    ];
                } else {
                    // MCR/MRC, page A8-493
                    let CRm = word as u8 & 0b1111;
                    let opc2 = (word >> 5) as u8 & 0b111;
                    let Rt = (word >> 12) as u8 & 0b1111;
                    let CRn = (word >> 16) as u8 & 0b1111;

                    let opc1 = (word >> 21) as u8 & 0b111;
                    if (word >> 20) & 1 == 0 {
                        inst.opcode = Opcode::MCR(coproc, opc1, opc2, false);
                    } else {
                        inst.opcode = Opcode::MRC(coproc, opc1, opc2, false);
                    }
                    inst.operands = [
                        Operand::Reg(Reg::from_u8(Rt)),
                        Operand::CReg(CReg::from_u8(CRn)),
                        Operand::CReg(CReg::from_u8(CRm)),
                        Operand::Nothing,
                    ];
                }
            }
            _ => { unreachable!("opc category is three bits"); }
        }
        Ok(())
    }
}

/// a struct with a summary of the `ARMv7` instruction set in an associated `impl Arch for ARMv7`.
#[cfg_attr(feature="use-serde", derive(Serialize, Deserialize))]
#[derive(Debug)]
pub struct ARMv7;

impl Arch for ARMv7 {
    type Address = u32;
    type Word = u8;
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
