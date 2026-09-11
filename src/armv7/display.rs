use core::fmt;
#[allow(deprecated)]
use crate::yaxpeax_arch::{Colorize, ShowContextual, YaxColors};
use crate::armv7::OperandVisitor;
use super::{Operand, Opcode, ShiftStyle, RegShift, RegShiftStyle, Reg, Bank, ConditionCode, ConditionedOpcode, Instruction, CReg, StatusRegMask};
use super::NoContext;
use yaxpeax_arch::display::DisplaySink;

trait DisplaySinkExt {
    fn write_reg(&mut self, gpr_num: u8) -> Result<(), core::fmt::Error>;
}

impl<T: DisplaySink> DisplaySinkExt for T {
    #[inline(always)]
    fn write_reg(&mut self, gpr_num: u8) -> Result<(), core::fmt::Error> {
        self.span_start_register();
        let name = REG_NAMES.get(gpr_num as usize)
            .unwrap_or_else(|| unsafe { core::hint::unreachable_unchecked() });
        unsafe {
            self.write_lt_8(name)?;
        }
        self.span_end_register();
        Ok(())
    }
}

/// an instruction and display settings to configure [`Display](fmt::Display)-formatting of the
/// instruction.
///
/// ARM instructions do not currently have configurable display behavior, but when they do, this
/// will be the place to configure it.
#[cfg(feature="fmt")]
pub struct InstructionDisplayer<'instr> {
    #[allow(dead_code)]
    pub(crate) instr: &'instr Instruction,
}

#[cfg(feature="fmt")]
impl<'instr> fmt::Display for InstructionDisplayer<'instr> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.instr)
    }
}

impl Instruction {
    /// wrap a reference to this instruction to format the instruction later.
    #[cfg(feature="fmt")]
    pub fn display<'instr>(&'instr self) -> InstructionDisplayer<'instr> {
        InstructionDisplayer {
            instr: self
        }
    }

    fn write_conditioned_opcode<T: DisplaySink>(&self, opc: &Opcode, f: &mut T) -> Result<(), fmt::Error> {
        unsafe {
            f.write_lt_8(opc.name())?;
        }
        // test/compare instructions always set flags and are consequently encoded with bit 20 set
        // as most other instructions that sets flags are. because these instructions
        // unconditionally set flags, though, their mnemonic skips the `s` suffix.
        if self.s() {
            let always_sets_flags =
                *opc == Opcode::CMP ||
                *opc == Opcode::CMN ||
                *opc == Opcode::TST ||
                *opc == Opcode::TEQ;
            if !always_sets_flags {
                f.write_char('s')?;
            }
        }
        if self.condition != ConditionCode::AL {
            let name = self.condition.name();
            // all condition codes are two characters long
            f.write_char(name[0] as char)?;
            f.write_char(name[1] as char)?;
        }
        if self.w() {
            f.write_fixed_size(".w")?;
        }
        Ok(())
    }
}

struct DisplayingOperandVisitor<'a, T> {
    f: &'a mut T,
}

static REG_NAMES: [&'static str; 16] = [
    "r0", "r1", "r2", "r3",
    "r4", "r5", "r6", "r7",
    "r8", "sb", "r10", "fp",
    "ip", "sp", "lr", "pc",
];

impl<T: DisplaySink> DisplayingOperandVisitor<'_, T> {
    fn emit_shift_type(&mut self, stype: ShiftStyle) -> Result<(), core::fmt::Error> {
        // shifter names in armv7 are all three characters.
        let name = stype.name();
        self.f.write_char(name[0] as char)?;
        self.f.write_char(name[1] as char)?;
        self.f.write_char(name[2] as char)?;

        Ok(())
    }

    fn format_reg_shift(&mut self, shift: RegShift) -> Result<(), core::fmt::Error> {
        match shift.into_shift() {
            RegShiftStyle::RegImm(imm_shift) => {
                self.f.write_reg(imm_shift.shiftee().number())?;
                let stype = imm_shift.stype();
                if imm_shift.imm() != 0 || stype != ShiftStyle::LSL {
                    self.f.write_fixed_size(", ")?;
                    self.emit_shift_type(stype)?;
                    if stype != ShiftStyle::RRX {
                        self.f.write_char(' ')?;
                        let sh = imm_shift.imm();
                        if sh >= 30 {
                            self.f.write_char('3')?;
                            self.f.write_char((sh - 30 + 0x30) as char)?;
                        } else if sh >= 20 {
                            self.f.write_char('2')?;
                            self.f.write_char((sh - 20 + 0x30) as char)?;
                        } else if sh >= 10 {
                            self.f.write_char('1')?;
                            self.f.write_char((sh - 10 + 0x30) as char)?;
                        } else {
                            self.f.write_char((sh + 0x30) as char)?;
                        }
                    }
                }
            }
            RegShiftStyle::RegReg(reg_shift) => {
                self.f.write_reg(reg_shift.shiftee().number())?;
                self.f.write_fixed_size(", ")?;
                self.emit_shift_type(reg_shift.stype())?;
                self.f.write_char(' ')?;
                self.f.write_reg(reg_shift.shifter().number())?;
            },
        }

        Ok(())
    }
}

impl<T: DisplaySink> crate::armv7::OperandVisitor for DisplayingOperandVisitor<'_, T> {
    type Ok = ();
    type Error = core::fmt::Error;

    fn visit_reglist(&mut self, mut list: u16) -> Result<Self::Ok, Self::Error> {
        self.f.write_char('{')?;
        let mut i = 0;
        let mut tail = false;
        while i < 16 {
            if (list & 1) == 1 {
                if tail {
                    self.f.write_fixed_size(", ")?;
                } else {
                    tail = true;
                }
                self.f.write_reg(i)?;
            }
            i += 1;
            list = list >> 1;
        }
        self.f.write_char('}')?;
        Ok(())
    }

    fn visit_banked_reg(&mut self, bank: Bank, reg: u16) -> Result<Self::Ok, Self::Error> {
        self.f.span_start_register();
        unsafe {
            self.f.write_lt_8(REG_NAMES[reg as usize])?;
        }
        self.f.write_char('_')?;
        self.f.write_fixed_size(bank.name())?;
        self.f.span_end_register();
        Ok(())
    }

    fn visit_banked_spsr(&mut self, bank: Bank) -> Result<Self::Ok, Self::Error> {
        self.f.span_start_register();
        self.f.write_fixed_size("spsr_")?;
        self.f.write_fixed_size(bank.name())?;
        self.f.span_end_register();
        Ok(())
    }

    fn visit_reg(&mut self, reg: Reg) -> Result<Self::Ok, Self::Error> {
        self.f.write_reg(reg.number())?;
        Ok(())
    }

    fn visit_reg_deref(&mut self, reg: Reg) -> Result<Self::Ok, Self::Error> {
        self.f.write_char('[')?;
        self.f.write_reg(reg.number())?;
        self.f.write_char(']')?;
        Ok(())
    }

    fn visit_reg_shift(&mut self, shift: RegShift) -> Result<Self::Ok, Self::Error> {
        self.format_reg_shift(shift)?;
        Ok(())
    }

    fn visit_reg_wback(&mut self, reg: Reg, wback: bool) -> Result<Self::Ok, Self::Error> {
        self.f.write_reg(reg.number())?;
        if wback {
            self.f.write_char('!')?;
        }
        Ok(())
    }

    fn visit_reg_deref_postindex_reg_shift(&mut self, base: Reg, index: RegShift, add: bool, wback: bool) -> Result<Self::Ok, Self::Error> {
        // TODO:
        assert!(!wback);
        self.f.write_char('[')?;
        self.f.write_reg(base.number())?;
        self.f.write_fixed_size("], ")?;
        if !add {
            self.f.write_char('-')?;
        }
        self.f.write_char(' ')?;
        self.format_reg_shift(index)?;
        Ok(())
    }

    fn visit_reg_deref_preindex_reg_shift(&mut self, base: Reg, index: RegShift, add: bool, wback: bool) -> Result<Self::Ok, Self::Error> {
        self.f.write_char('[')?;
        self.f.write_reg(base.number())?;
        self.f.write_fixed_size(", ")?;
        if !add {
            self.f.write_char('-')?;
        }
        self.format_reg_shift(index)?;
        self.f.write_char(']')?;
        if wback {
            self.f.write_char('!')?;
        }
        Ok(())
    }

    // TODO: post-index with writeback is a bug right..?
    fn visit_reg_deref_postindex_offset(&mut self, base: Reg, offset: u16, add: bool, _wback: bool) -> Result<Self::Ok, Self::Error> {
        self.f.write_char('[')?;
        self.f.write_reg(base.number())?;
        self.f.write_char(']')?;

        if offset != 0 {
            self.f.write_fixed_size(", ")?;
            if !add {
                self.f.write_char('-')?;
            }
            self.f.write_prefixed_u16(offset)?;
        }
        Ok(())
    }

    fn visit_reg_deref_preindex_offset(&mut self, base: Reg, offset: u16, add: bool, wback: bool) -> Result<Self::Ok, Self::Error> {
        self.f.write_char('[')?;
        self.f.write_reg(base.number())?;
        if offset != 0 {
            self.f.write_fixed_size(", ")?;
            if !add {
                self.f.write_char('-')?;
            }
            self.f.write_prefixed_u16(offset)?;
        }
        self.f.write_char(']')?;
        if wback {
            self.f.write_char('!')?;
        }
        Ok(())
    }

    fn visit_reg_deref_postindex_reg(&mut self, base: Reg, offset: Reg, add: bool, wback: bool) -> Result<Self::Ok, Self::Error> {
        self.f.write_char('[')?;
        self.f.write_reg(base.number())?;
        self.f.write_fixed_size("], ")?;
        if !add {
            self.f.write_char('-')?;
        }
        self.f.write_reg(offset.number())?;
        if wback {
            self.f.write_char('!')?;
        }
        Ok(())
    }

    fn visit_reg_deref_preindex_reg(&mut self, base: Reg, offset: Reg, add: bool, wback: bool) -> Result<Self::Ok, Self::Error> {
        self.f.write_char('[')?;
        self.f.write_reg(base.number())?;
        self.f.write_fixed_size(", ")?;
        if !add {
            self.f.write_char('-')?;
        }
        self.f.write_reg(offset.number())?;
        self.f.write_char(']')?;

        if wback {
            self.f.write_char('!')?;
        }
        Ok(())
    }

    fn visit_imm12(&mut self, imm: u16) -> Result<Self::Ok, Self::Error> {
        self.f.write_char('#')?;
        self.f.write_prefixed_u16(imm)
    }

    fn visit_imm32(&mut self, imm: u32) -> Result<Self::Ok, Self::Error> {
        self.f.write_char('#')?;
        self.f.write_prefixed_u32(imm)
    }

    fn visit_branch_offset(&mut self, offset: i32) -> Result<Self::Ok, Self::Error> {
        self.f.write_char('$')?;
        if offset >= 0 {
            self.f.write_char('+')?;
        }
        self.f.write_prefixed_i32(offset << 2)
    }

    fn visit_blx_offset(&mut self, offset: i32) -> Result<Self::Ok, Self::Error> {
        self.f.write_char('$')?;
        if offset >= 0 {
            self.f.write_char('+')?;
        }
        self.f.write_prefixed_i32(offset << 1)
    }

    fn visit_coprocessor_option(&mut self, nr: u8) -> Result<Self::Ok, Self::Error> {
        self.f.write_char('{')?;
        self.f.write_prefixed_u8(nr)?;
        self.f.write_char('}')?;
        Ok(())
    }

    fn visit_creg(&mut self, creg: CReg) -> Result<Self::Ok, Self::Error> {
        self.f.span_start_register();
        self.f.write_char('c')?;
        let num = creg.number();
        if num >= 10 {
            self.f.write_char('1')?;
            // num is at most 16
            self.f.write_char((num - 10 + 0x30) as char)?;
        } else {
            self.f.write_char((num + 0x30) as char)?;
        }
        self.f.span_end_register();
        Ok(())
    }

    fn visit_status_reg_mask(&mut self, mask: StatusRegMask) -> Result<Self::Ok, Self::Error> {
        self.f.span_start_register();
        self.f.write_fixed_size(mask.name())?;
        self.f.span_end_register();
        Ok(())
    }

    fn visit_rotate(&mut self, amt: u8) -> Result<Self::Ok, Self::Error> {
        self.emit_shift_type(ShiftStyle::ROR)?;
        self.f.write_char(' ')?;
        self.f.write_prefixed_u16(amt as u16)?;
        Ok(())
    }

    fn visit_apsr(&mut self) -> Result<Self::Ok, Self::Error> {
        self.f.span_start_register();
        self.f.write_fixed_size("apsr")?;
        self.f.span_end_register();
        Ok(())
    }

    fn visit_spsr(&mut self) -> Result<Self::Ok, Self::Error> {
        self.f.span_start_register();
        self.f.write_fixed_size("spsr")?;
        self.f.span_end_register();
        Ok(())
    }

    fn visit_cpsr(&mut self) -> Result<Self::Ok, Self::Error> {
        self.f.span_start_register();
        self.f.write_fixed_size("cpsr")?;
        self.f.span_end_register();
        Ok(())
    }

    fn visit_other(&mut self) -> Result<Self::Ok, Self::Error> {
        Ok(())
    }
}

fn write_coproc<T: DisplaySink>(coproc: u8, out: &mut T) -> fmt::Result {
    // coproc is a 4-bit field
    debug_assert!(coproc < 16);

    out.write_char('p')?;
    if coproc < 10 {
        out.write_char((coproc + 0x30) as char)
    } else {
        out.write_char('1')?;
        out.write_char((coproc - 10 + 0x30) as char)
    }
}

#[allow(non_snake_case)]
pub(crate) fn visit_inst<T: DisplaySink>(instr: &Instruction, out: &mut T) -> fmt::Result {
    // handle a few instruction aliasing cases first...
    match instr.opcode {
        Opcode::LDR => {
            match instr.operands {
                // TODO: should this be PostindexOffset?
                [Operand::Reg(Rt), Operand::RegDerefPostindexOffset(Reg { bits: 13 }, 4, true, false), Operand::Nothing, Operand::Nothing] => {
                    out.span_start_opcode();
                    instr.write_conditioned_opcode(&Opcode::POP, out)?;
                    out.span_end_opcode();

                    out.write_char(' ')?;
                    out.write_char('{')?;
                    out.span_start_register();
                    out.write_reg(Rt.number())?;
                    out.span_end_register();
                    out.write_char('}')?;
                    return Ok(());
                },
                _ => {}
            }
        },
        Opcode::STR => {
            match instr.operands {
                // TODO: should this be PreindexOffset?
                [Operand::Reg(Rt), Operand::RegDerefPreindexOffset(Reg { bits: 13 }, 4, false, true), Operand::Nothing, Operand::Nothing] => {
                    out.span_start_opcode();
                    instr.write_conditioned_opcode(&Opcode::PUSH, out)?;
                    out.span_end_opcode();

                    out.write_char(' ')?;

                    out.write_char('{')?;
                    out.span_start_register();
                    out.write_reg(Rt.number())?;
                    out.span_end_register();
                    out.write_char('}')?;
                    return Ok(());
                },
                _ => {}
            }
        },
        Opcode::LDM(true, false, false, _usermode) => {
            // TODO: what indicates usermode in the ARM syntax?
            match instr.operands {
                [Operand::RegWBack(Reg { bits: 13 }, true), Operand::RegList(list), Operand::Nothing, Operand::Nothing] => {
                    out.span_start_opcode();
                    instr.write_conditioned_opcode(&Opcode::POP, out)?;
                    out.span_end_opcode();

                    out.write_char(' ')?;

                    let mut visitor = DisplayingOperandVisitor {
                        f: out,
                    };
                    visitor.visit_reglist(list)?;
                    return Ok(());
                }
                _ => {}
            }
        }
        Opcode::STM(false, true, false, _usermode) => {
            // TODO: what indicates usermode in the ARM syntax?
            match instr.operands {
                [Operand::RegWBack(Reg { bits: 13 }, true), Operand::RegList(list), Operand::Nothing, Operand::Nothing] => {
                    out.span_start_opcode();
                    instr.write_conditioned_opcode(&Opcode::PUSH, out)?;
                    out.span_end_opcode();

                    out.write_char(' ')?;

                    let mut visitor = DisplayingOperandVisitor {
                        f: out,
                    };
                    visitor.visit_reglist(list)?;
                    return Ok(());
                }
                _ => {}
            }
        }
        Opcode::STCL(coproc, _) |
        Opcode::STC(coproc, _) |
        Opcode::LDC(coproc, _) |
        Opcode::LDCL(coproc, _) => {
            out.span_start_opcode();
            unsafe {
                out.write_lt_8(instr.opcode.name())?;
            }
            if instr.condition != ConditionCode::AL {
                let name = instr.condition.name();
                // all condition codes are two characters long
                out.write_char(name[0] as char)?;
                out.write_char(name[1] as char)?;
            }
            out.span_end_opcode();
            out.write_fixed_size(" p")?;
            if coproc >= 10 {
                out.write_char('1')?;
                out.write_char((coproc - 10 + 0x30) as char)?;
            } else {
                out.write_char((coproc + 0x30) as char)?;
            }

            let ops = instr.operands.iter();
            for op in ops {
                if let Operand::Nothing = op {
                    break;
                }
                out.write_fixed_size(", ")?;
                let mut op_visitor = DisplayingOperandVisitor {
                    f: out
                };
                op.visit(&mut op_visitor)?;
            }

            return Ok(());
        }
        Opcode::MRRC(coproc, opc, _) |
        Opcode::MCRR(coproc, opc, _) => {
            out.span_start_opcode();
            unsafe {
                out.write_lt_8(instr.opcode.name())?;
            }
            if instr.condition != ConditionCode::AL {
                let name = instr.condition.name();
                // all condition codes are two characters long
                out.write_char(name[0] as char)?;
                out.write_char(name[1] as char)?;
            }
            out.span_end_opcode();

            out.write_char(' ')?;
            write_coproc(coproc, out)?;
            out.write_fixed_size(", ")?;
            // mrc/mcr have 3-bit opc1, but mrrc/mcrr have 4-bit opc1
            if opc >= 10 {
                out.write_char('1')?;
                out.write_char((opc - 10 + 0x30) as char)?;
            } else {
                out.write_char((opc + 0x30) as char)?;
            }

            let ops = instr.operands.iter();
            for op in ops {
                if let Operand::Nothing = op {
                    break;
                }
                out.write_fixed_size(", ")?;
                let mut op_visitor = DisplayingOperandVisitor {
                    f: out
                };
                op.visit(&mut op_visitor)?;
            }

            return Ok(());
        }
        Opcode::LSL => {
            if instr.operands[2] == Operand::Imm12(0) {
                out.span_start_opcode();
                out.write_str("mov")?;
                if instr.s() {
                    out.write_char('s')?;
                }
                out.span_end_opcode();

                out.write_str(" ")?;

                let mut op_visitor = DisplayingOperandVisitor {
                    f: out
                };
                instr.operands[0].visit(&mut op_visitor)?;
                op_visitor.f.write_str(", ")?;
                instr.operands[1].visit(&mut op_visitor)?;
                return Ok(());
            }
        }
        Opcode::MRC(coproc, opc1, opc2, _) |
        Opcode::MCR(coproc, opc1, opc2, _) |
        Opcode::CDP(coproc, opc1, opc2, _) => {
            out.span_start_opcode();
            unsafe {
                out.write_lt_8(instr.opcode.name())?;
            }
            if instr.condition != ConditionCode::AL {
                let name = instr.condition.name();
                // all condition codes are two characters long
                out.write_char(name[0] as char)?;
                out.write_char(name[1] as char)?;
            }
            out.span_end_opcode();

            out.write_char(' ')?;
            write_coproc(coproc, out)?;
            out.write_fixed_size(", ")?;
            // opc1 is a 3-bit field for MCR and MRC, but is four bits for CDP
            if opc1 >= 10 {
                out.write_char('1')?;
                out.write_char((opc1 - 10 + 0x30) as char)?;
            } else {
                out.write_char((opc1 + 0x30) as char)?;
            }

            let ops = instr.operands.iter();
            for op in ops {
                if let Operand::Nothing = op {
                    break;
                }
                out.write_fixed_size(", ")?;
                let mut op_visitor = DisplayingOperandVisitor {
                    f: out
                };
                op.visit(&mut op_visitor)?;
            }

            out.write_fixed_size(", ")?;
            // opc2 is a 3-bit field
            out.write_char((opc2 + 0x30) as char)?;

            return Ok(());
        }
        _ => {}
    }

    // no aliasing, just print the opcode itself
    out.span_start_opcode();
    instr.write_conditioned_opcode(&instr.opcode, out)?;
    // don't end the opcode yet because some include a few extra characters after the mnemonic.

    if instr.opcode == Opcode::IT {
        let (Operand::Imm32(cond), Operand::Imm32(mask)) = (&instr.operands[0], &instr.operands[1]) else {
            panic!("impossible it operand");
        };

        let (inv, condition) = if *cond == 0b1111 {
            // we've allowed *unpredictable* instruction encodings. capstone calls this condition
            // "al" as well, so might as well follow along... and for this condition code it
            // doesn't invert the fields either!
            (false, ConditionCode::AL)
        } else {
            let inv = cond & 1 == 1;
            (inv, ConditionCode::build(*cond as u8))
        };
        if mask & 0b0001 != 0 {
            // three flags
            out.write_char(if inv ^ ((mask & 0b1000) != 0) { 'e' } else { 't' })?;
            out.write_char(if inv ^ ((mask & 0b0100) != 0) { 'e' } else { 't' })?;
            out.write_char(if inv ^ ((mask & 0b0010) != 0) { 'e' } else { 't' })?;
        } else if mask & 0b0010 != 0 {
            // two flags
            out.write_char(if inv ^ ((mask & 0b1000) != 0) { 'e' } else { 't' })?;
            out.write_char(if inv ^ ((mask & 0b0100) != 0) { 'e' } else { 't' })?;
        } else if mask & 0b0100 != 0 {
            // one flag
            out.write_char(if inv ^ ((mask & 0b1000) != 0) { 'e' } else { 't' })?;
        } else {
            // no flags
        }
        out.span_end_opcode();

        out.write_char(' ')?;
        let name = condition.name();
        // all condition codes are two characters long
        out.write_char(name[0] as char)?;
        out.write_char(name[1] as char)?;
        return Ok(());
    }

    out.span_end_opcode();

    match instr.opcode {
        Opcode::CPS(_) => {
            if let Operand::Imm12(aif) = &instr.operands[0] {
                let mut comma = false;

                if *aif != 0 {
                    out.write_char(' ')?;
                    if aif & 0b100 != 0 { out.write_char('a')?; }
                    if aif & 0b010 != 0 { out.write_char('i')?; }
                    if aif & 0b001 != 0 { out.write_char('f')?; }
                    // we wrote something for the first operand after all, so include a comma
                    comma = true;
                }
                if let Operand::Imm12(mode) = &instr.operands[1] {
                    if comma { out.write_char(',')?; }
                    out.write_fixed_size(" #")?;
                    out.write_prefixed_u16(*mode)?;
                }
                return Ok(());
            } else {
                panic!("impossible cps operand");
            }
        }
        Opcode::SETEND => {
            if let Operand::Imm12(i) = &instr.operands[0] {
                out.write_char(' ')?;
                if *i == 0 {
                    out.write_fixed_size("le")?;
                } else {
                    out.write_fixed_size("be")?;
                }
                return Ok(());
            } else {
                panic!("impossible setend operand");
            }
        }

        _ => {}
    }

    match instr.opcode {
        // TODO: [add, pre, usermode]
        Opcode::STM(_add, _pre, _wback, _usermode) |
        Opcode::LDM(_add, _pre, _wback, _usermode) => {
            match instr.operands {
                [Operand::RegWBack(Rr, wback), Operand::RegList(list), Operand::Nothing, Operand::Nothing] => {
                    out.write_char(' ')?;
                    out.write_reg(Rr.number())?;
                    if wback { out.write_char('!')?; }
                    out.write_fixed_size(", ")?;
                    let mut op_visitor = DisplayingOperandVisitor {
                        f: out,
                    };
                    op_visitor.visit_reglist(list)?;
                    return Ok(());
                },
                _ => { unreachable!(); }
            }
        },
        _ => {}
    }

    let mut ops = instr.operands.iter();
    if let Some(first_op) = ops.next() {
        if let Operand::Nothing = first_op {
            return Ok(());
        }
        out.write_char(' ')?;
        let mut op_visitor = DisplayingOperandVisitor {
            f: out
        };
        first_op.visit(&mut op_visitor)?;
    } else {
        return Ok(());
    }

    for op in ops {
        if let Operand::Nothing = op {
            break;
        }
        out.write_fixed_size(", ")?;
        let mut op_visitor = DisplayingOperandVisitor {
            f: out
        };
        op.visit(&mut op_visitor)?;
    }

    Ok(())
}

#[allow(non_snake_case)]
#[allow(deprecated)]
impl <T: fmt::Write, Y: YaxColors> ShowContextual<u32, NoContext, T, Y> for Instruction {
    fn contextualize(&self, _colors: &Y, _address: u32, _context: Option<&NoContext>, out: &mut T) -> fmt::Result {
        let mut f = yaxpeax_arch::display::FmtSink::new(out);
        visit_inst(self, &mut f)
    }
}

#[allow(deprecated)]
impl <T: fmt::Write, Y: YaxColors> Colorize<T, Y> for ConditionedOpcode {
    fn colorize(&self, colors: &Y, out: &mut T) -> fmt::Result {
        match self.0 {
            Opcode::UDF |
            Opcode::Invalid => { write!(out, "{}", colors.invalid_op(self)) },
            Opcode::TBB |
            Opcode::TBH |
            Opcode::CBZ |
            Opcode::CBNZ |
            Opcode::IT |
            Opcode::B |
            Opcode::BL |
            Opcode::BLX |
            Opcode::BX |
            Opcode::BXJ => { write!(out, "{}", colors.control_flow_op(self)) },

            Opcode::AND |
            Opcode::EOR |
            Opcode::ORR |
            Opcode::ORN |
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

            Opcode::QADD |
            Opcode::QSUB |
            Opcode::QDADD |
            Opcode::QDSUB |

            Opcode::SADD16 |
            Opcode::QADD16 |
            Opcode::SHADD16 |
            Opcode::SASX |
            Opcode::QASX |
            Opcode::SHASX |
            Opcode::SSAX |
            Opcode::QSAX |
            Opcode::SHSAX |
            Opcode::SSUB16 |
            Opcode::QSUB16 |
            Opcode::SHSUB16 |
            Opcode::SADD8 |
            Opcode::QADD8 |
            Opcode::SHADD8 |
            Opcode::SSUB8 |
            Opcode::QSUB8 |
            Opcode::SHSUB8 |
            Opcode::UADD16 |
            Opcode::UQADD16 |
            Opcode::UHADD16 |
            Opcode::UASX |
            Opcode::UQASX |
            Opcode::UHASX |
            Opcode::USAX |
            Opcode::UQSAX |
            Opcode::UHSAX |
            Opcode::USUB16 |
            Opcode::UQSUB16 |
            Opcode::UHSUB16 |
            Opcode::UADD8 |
            Opcode::UQADD8 |
            Opcode::UHADD8 |
            Opcode::USUB8 |
            Opcode::UQSUB8 |
            Opcode::UHSUB8 |

            Opcode::CLZ |

            Opcode::MUL |
            Opcode::MLA |
            Opcode::UMAAL |
            Opcode::MLS |
            Opcode::UMULL |
            Opcode::UMLAL |
            Opcode::SMLSD |
            Opcode::SMMLA |
            Opcode::SMMLS |
            Opcode::USADA8 |
            Opcode::USAD8 |
            Opcode::SDIV |
            Opcode::UDIV |
            Opcode::SMLALD(_) |
            Opcode::SMLSLD(_) |
            Opcode::SMLAD |
            Opcode::SMUSD |
            Opcode::SMMUL |
            Opcode::SMULW(_) |
            Opcode::SMUAD |
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

            Opcode::LDRSH |
            Opcode::LDRSHT |
            Opcode::LDRSB |
            Opcode::LDRSBT |
            Opcode::STRD |
            Opcode::LDRD |
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
            Opcode::LDR |
            Opcode::STR |
            Opcode::LDRH |
            Opcode::STRH |
            Opcode::LDRB |
            Opcode::STRB |
            Opcode::LDRT |
            Opcode::STRT |
            Opcode::LDRHT |
            Opcode::STRHT |
            Opcode::LDRBT |
            Opcode::STRBT |
            Opcode::STLB |
            Opcode::STLH |
            Opcode::STL |
            Opcode::STLEXB |
            Opcode::STLEXH |
            Opcode::STLEX |
            Opcode::STLEXD |
            Opcode::LDAB |
            Opcode::LDAH |
            Opcode::LDA |
            Opcode::LDAEXB |
            Opcode::LDAEXH |
            Opcode::LDAEX |
            Opcode::LDAEXD |
            Opcode::SWP |
            Opcode::SWPB |
            Opcode::MSR |
            Opcode::MRS |
            Opcode::CLREX |
            Opcode::SXTAB |
            Opcode::SXTAB16 |
            Opcode::SXTAH |
            Opcode::SXTB |
            Opcode::SXTB16 |
            Opcode::SXTH |
            Opcode::UXTAB |
            Opcode::UXTAB16 |
            Opcode::UXTAH |
            Opcode::UXTB |
            Opcode::UXTB16 |
            Opcode::UXTH |
            Opcode::PKHTB |
            Opcode::PKHBT |
            Opcode::REV |
            Opcode::REV16 |
            Opcode::REVSH |
            Opcode::SSAT |
            Opcode::SSAT16 |
            Opcode::SBFX |
            Opcode::USAT |
            Opcode::USAT16 |
            Opcode::UBFX |
            Opcode::BFI |
            Opcode::BFC |
            Opcode::RBIT |
            Opcode::SEL |
            Opcode::MOV |
            Opcode::MOVT |
            Opcode::MVN => { write!(out, "{}", colors.data_op(self)) },

            Opcode::HINT |
            Opcode::NOP |
            Opcode::PLD |
            Opcode::PLI |
            Opcode::ISB |
            Opcode::DMB |
            Opcode::DSB |
            Opcode::CSDB |
            Opcode::SRS(_, _) |
            Opcode::TT { .. } |
            Opcode::BKPT => { write!(out, "{}", colors.misc_op(self)) },

            Opcode::DBG |
            Opcode::CPS(_) |
            Opcode::CPS_modeonly |
            Opcode::SETEND |
            Opcode::ENTERX |
            Opcode::LEAVEX |
            Opcode::YIELD |
            Opcode::WFE |
            Opcode::WFI |
            Opcode::PACBTI |
            Opcode::BTI |
            Opcode::ESB |
            Opcode::PAC |
            Opcode::AUT |
            Opcode::SEV |
            Opcode::ERET |
            Opcode::RFE(_, _) |
            Opcode::HVC |
            Opcode::SVC |
            Opcode::SMC |
            Opcode::LDC(_, _) |
            Opcode::LDCL(_, _) |
            Opcode::STC(_, _) |
            Opcode::STCL(_, _) |
            Opcode::MCRR(_, _, _) |
            Opcode::MCR(_, _, _, _) |
            Opcode::MRRC(_, _, _) |
            Opcode::MRC(_, _, _, _) |
            Opcode::CDP(_, _, _, _) => { write!(out, "{}", colors.platform_op(self)) },
        }
    }
}

impl fmt::Display for Opcode {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let mut f = yaxpeax_arch::display::FmtSink::new(f);
        self.write_to_sink(&mut f)
    }
}

impl Opcode {
    fn write_to_sink<T: DisplaySink>(&self, sink: &mut T) -> Result<(), fmt::Error> {
        sink.write_str(self.name())
    }

    fn name(&self) -> &'static str {
        match self {
            Opcode::LDRSH => { "ldrsh" },
            Opcode::LDRSHT => { "ldrsht" },
            Opcode::LDRSB => { "ldrsb" },
            Opcode::LDRSBT => { "ldrsbt" },
            Opcode::STRD => { "strd" },
            Opcode::LDRD => { "ldrd" },
            Opcode::LDC(_, false) => { "ldc" },
            Opcode::LDC(_, true) => { "ldc2" },
            Opcode::LDCL(_, false) => { "ldcl" },
            Opcode::LDCL(_, true) => { "ldc2l" },
            Opcode::STC(_, false) => { "stc" },
            Opcode::STC(_, true) => { "stc2" },
            Opcode::STCL(_, false) => { "stcl" },
            Opcode::STCL(_, true) => { "stc2l" },
            Opcode::MCR(_, _, _, false) => { "mcr" },
            Opcode::MCR(_, _, _, true) => { "mcr2" },
            Opcode::MRC(_, _, _, false) => { "mrc" },
            Opcode::MRC(_, _, _, true) => { "mrc2" },
            Opcode::MCRR(_, _, false) => { "mcrr" },
            Opcode::MCRR(_, _, true) => { "mcrr2" },
            Opcode::MRRC(_, _, false) => { "mrrc" },
            Opcode::MRRC(_, _, true) => { "mrrc2" },
            Opcode::CDP(_, _, _, false) => { "cdp" },
            Opcode::CDP(_, _, _, true) => { "cdp2" },
            Opcode::SRS(true, true) => { "srsib" },
            Opcode::SRS(false, true) => { "srsia" },
            Opcode::SRS(true, false) => { "srsdb" },
            Opcode::SRS(false, false) => { "srsda" },
            Opcode::RFE(true, true) => { "rfeib" },
            Opcode::RFE(false, true) => { "rfeia" },
            Opcode::RFE(true, false) => { "rfedb" },
            Opcode::RFE(false, false) => { "rfeda" },
            Opcode::ERET => { "eret" },
            Opcode::HVC => { "hvc" },
            Opcode::BKPT => { "bkpt" },
            Opcode::SMC => { "smc" },
            Opcode::MOVT => { "movt" },
            Opcode::QADD => { "qadd" },
            Opcode::QSUB => { "qsub" },
            Opcode::QDADD => { "qdadd" },
            Opcode::QDSUB => { "qdsub" },
            Opcode::Invalid => { "invalid" },
            Opcode::POP => { "pop" },
            Opcode::PUSH => { "push" },
            Opcode::B => { "b" },
            Opcode::BL => { "bl" },
            Opcode::BLX => { "blx" },
            Opcode::BX => { "bx" },
            Opcode::BXJ => { "bxj" },
            Opcode::CLZ => { "clz" },
            Opcode::AND => { "and" },
            Opcode::EOR => { "eor" },
            Opcode::SUB => { "sub" },
            Opcode::RSB => { "rsb" },
            Opcode::ADD => { "add" },
            Opcode::ADC => { "adc" },
            Opcode::SBC => { "sbc" },
            Opcode::RSC => { "rsc" },
            Opcode::TST => { "tst" },
            Opcode::TEQ => { "teq" },
            Opcode::CMP => { "cmp" },
            Opcode::CMN => { "cmn" },
            Opcode::ORR => { "orr" },
            Opcode::MOV => { "mov" },
            Opcode::MSR => { "msr" },
            Opcode::MRS => { "mrs" },
            Opcode::BIC => { "bic" },
            Opcode::MVN => { "mvn" },
            Opcode::LSL => { "lsl" },
            Opcode::LSR => { "lsr" },
            Opcode::ASR => { "asr" },
            Opcode::RRX => { "rrx" },
            Opcode::ROR => { "ror" },
            Opcode::ADR => { "adr" },
            Opcode::LDREXH => { "ldrexh" },
            Opcode::STREXH => { "strexh" },
            Opcode::LDREXB => { "ldrexb" },
            Opcode::STREXB => { "strexb" },
            Opcode::LDREXD => { "ldrexd" },
            Opcode::STREXD => { "strexd" },
            Opcode::LDREX => { "ldrex" },
            Opcode::STREX => { "strex" },
            Opcode::LDM(false, false, _, _) => { "ldmda" },
            Opcode::LDM(false, true, _, _) => { "ldmdb" },
            // TODO: seems like these are backwards
            Opcode::LDM(true, false, _, _) => { "ldm" },
            Opcode::LDM(true, true, _, _) => { "ldmia" },
            Opcode::STM(false, false, _, _) => { "stmda" },
            Opcode::STM(false, true, _, _) => { "stmdb" },
            // TODO: seems like these are backwards
            Opcode::STM(true, false, _, _) => { "stm" },
            Opcode::STM(true, true, _, _) => { "stmia" },
            Opcode::LDR => { "ldr" },
            Opcode::STR => { "str" },
            Opcode::LDRH => { "ldrh" },
            Opcode::STRH => { "strh" },
            Opcode::LDRB => { "ldrb" },
            Opcode::STRB => { "strb" },
            Opcode::LDRT => { "ldrt" },
            Opcode::STRT => { "strt" },
            Opcode::LDRHT => { "ldrht" },
            Opcode::STRHT => { "strht" },
            Opcode::LDRBT => { "ldrbt" },
            Opcode::STRBT => { "strbt" },
            Opcode::STLB => { "stlb" },
            Opcode::STLH => { "stlh" },
            Opcode::STL => { "stl" },
            Opcode::STLEXB => { "stlexb" },
            Opcode::STLEXH => { "stlexh" },
            Opcode::STLEX => { "stlex" },
            Opcode::STLEXD => { "stlexd" },
            Opcode::LDAB => { "ldab" },
            Opcode::LDAH => { "ldah" },
            Opcode::LDA => { "lda" },
            Opcode::LDAEXB => { "ldaexb" },
            Opcode::LDAEXH => { "ldaexh" },
            Opcode::LDAEX => { "ldaex" },
            Opcode::LDAEXD => { "ldaexd" },
            Opcode::SWP => { "swp" },
            Opcode::SWPB => { "swpb" },
            Opcode::SDIV => { "sdiv" },
            Opcode::UDIV => { "udiv" },
            Opcode::MUL => { "mul" },
            Opcode::MLA => { "mla" },
            Opcode::UMAAL => { "umaal" },
            Opcode::MLS => { "mls" },
            Opcode::UMULL => { "umull" },
            Opcode::UMLAL => { "umlal" },
            Opcode::SMULL => { "smull" },
            Opcode::SMLA(true, true) => { "smlatt" },
            Opcode::SMLA(true, false) => { "smlatb" },
            Opcode::SMLA(false, true) => { "smlabt" },
            Opcode::SMLA(false, false) => { "smlabb" },
            Opcode::SMLAL => { "smlal" },
            Opcode::SMLAL_halfword(true, true) => { "smlaltt" },
            Opcode::SMLAL_halfword(true, false) => { "smlaltb" },
            Opcode::SMLAL_halfword(false, true) => { "smlalbt" },
            Opcode::SMLAL_halfword(false, false) => { "smlalbb" },
            Opcode::SMUL(true, true) => { "smultt" },
            Opcode::SMUL(true, false) => { "smultb" },
            Opcode::SMUL(false, true) => { "smulbt" },
            Opcode::SMUL(false, false) => { "smulbb" },
            Opcode::SMAL(true, true) => { "smaltt" },
            Opcode::SMAL(true, false) => { "smaltb" },
            Opcode::SMAL(false, true) => { "smalbt" },
            Opcode::SMAL(false, false) => { "smalbb" },
            Opcode::SMLAW(true) => { "smlawt" },
            Opcode::SMLAW(false) => { "smlawb" },
            Opcode::SMULW(true) => { "smulwt" },
            Opcode::SMULW(false) => { "smulwb" },
            Opcode::SMLALD(true) => { "smlaldt" },
            Opcode::SMLALD(false) => { "smlaldb" },
            Opcode::SMLSLD(true) => { "smlsldt" },
            Opcode::SMLSLD(false) => { "smlsldb" },
            Opcode::SMLSD => { "smlsd" },
            Opcode::SMMLA => { "smmla" },
            Opcode::SMMLS => { "smmls" },
            Opcode::USADA8 => { "usada8" },
            Opcode::USAD8 => { "usad8" },
            Opcode::SMLAD => { "smlad" },
            Opcode::SMUSD => { "smusd" },
            Opcode::SMMUL => { "smmul" },
            Opcode::SMUAD => { "smuad" },
            Opcode::TBB => { "tbb" },
            Opcode::TBH => { "tbh" },
            Opcode::UDF => { "udf" },
            Opcode::SVC => { "svc" },
            Opcode::WFE => { "wfe" },
            Opcode::WFI => { "wfi" },
            Opcode::SEV => { "sev" },
            Opcode::CSDB => { "csdb" },
            Opcode::YIELD => { "yield" },
            Opcode::HINT => { "hint" },
            Opcode::NOP => { "nop" },
            Opcode::LEAVEX => { "leavex" },
            Opcode::ENTERX => { "enterx" },
            Opcode::CLREX => { "clrex" },
            Opcode::DSB => { "dsb" },
            Opcode::DMB => { "dmb" },
            Opcode::ISB => { "isb" },
            Opcode::SXTH => { "sxth" },
            Opcode::UXTH => { "uxth" },
            Opcode::SXTB16 => { "sxtb16" },
            Opcode::UXTB16 => { "uxtb16" },
            Opcode::SXTB => { "sxtb" },
            Opcode::UXTB => { "uxtb" },
            Opcode::SXTAH => { "sxtah" },
            Opcode::UXTAH => { "uxtah" },
            Opcode::SXTAB16 => { "sxtab16" },
            Opcode::UXTAB16 => { "uxtab16" },
            Opcode::SXTAB => { "sxtab" },
            Opcode::UXTAB => { "uxtab" },
            Opcode::CBZ => { "cbz" },
            Opcode::CBNZ => { "cbnz" },
            Opcode::SETEND => { "setend" },
            Opcode::CPS(true) => { "cpsid" },
            Opcode::CPS(false) => { "cpsie" },
            Opcode::CPS_modeonly => { "cps" },
            Opcode::REV => { "rev" },
            Opcode::REV16 => { "rev16" },
            Opcode::REVSH => { "revsh" },
            Opcode::IT => { "it" },
            Opcode::PKHTB => { "pkhtb" },
            Opcode::PKHBT => { "pkhbt" },
            Opcode::ORN => { "orn" },
            Opcode::SSAT => { "ssat" },
            Opcode::SSAT16 => { "ssat16" },
            Opcode::SBFX => { "sbfx" },
            Opcode::USAT => { "usat" },
            Opcode::USAT16 => { "usat16" },
            Opcode::UBFX => { "ubfx" },
            Opcode::BFI => { "bfi" },
            Opcode::BFC => { "bfc" },
            Opcode::DBG => { "dbg" },
            Opcode::PLD => { "pld" },
            Opcode::PLI => { "pli" },
            Opcode::RBIT => { "rbit" },
            Opcode::SEL => { "sel" },
            Opcode::SADD16 => { "sadd16" },
            Opcode::QADD16 => { "qadd16" },
            Opcode::SHADD16 => { "shadd16" },
            Opcode::SASX => { "sasx" },
            Opcode::QASX => { "qasx" },
            Opcode::SHASX => { "shasx" },
            Opcode::SSAX => { "ssax" },
            Opcode::QSAX => { "qsax" },
            Opcode::SHSAX => { "shsax" },
            Opcode::SSUB16 => { "ssub16" },
            Opcode::QSUB16 => { "qsub16" },
            Opcode::SHSUB16 => { "shsub16" },
            Opcode::SADD8 => { "sadd8" },
            Opcode::QADD8 => { "qadd8" },
            Opcode::SHADD8 => { "shadd8" },
            Opcode::SSUB8 => { "ssub8" },
            Opcode::QSUB8 => { "qsub8" },
            Opcode::SHSUB8 => { "shsub8" },
            Opcode::UADD16 => { "uadd16" },
            Opcode::UQADD16 => { "uqadd16" },
            Opcode::UHADD16 => { "uhadd16" },
            Opcode::UASX => { "uasx" },
            Opcode::UQASX => { "uqasx" },
            Opcode::UHASX => { "uhasx" },
            Opcode::USAX => { "usax" },
            Opcode::UQSAX => { "uqsax" },
            Opcode::UHSAX => { "uhsax" },
            Opcode::USUB16 => { "usub16" },
            Opcode::UQSUB16 => { "uqsub16" },
            Opcode::UHSUB16 => { "uhsub16" },
            Opcode::UADD8 => { "uadd8" },
            Opcode::UQADD8 => { "uqadd8" },
            Opcode::UHADD8 => { "uhadd8" },
            Opcode::USUB8 => { "usub8" },
            Opcode::UQSUB8 => { "uqsub8" },
            Opcode::UHSUB8 => { "uhsub8" },

            Opcode::TT { alternate: false, unprivileged: false } => "tt",
            Opcode::TT { alternate: true, unprivileged: false } => "tta",
            Opcode::TT { alternate: false, unprivileged: true } => "ttt",
            Opcode::TT { alternate: true, unprivileged: true } => "ttat",

            Opcode::PACBTI => { "pacbti" },
            Opcode::BTI => { "bti" },
            Opcode::ESB => { "esb" },
            Opcode::PAC => { "pac" },
            Opcode::AUT => { "aut" },
        }
    }
}

impl fmt::Display for Bank {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.name())
    }
}

impl Bank {
    fn name(&self) -> &'static str {
        match self {
            Bank::Usr => "usr",
            Bank::Fiq => "fiq",
            Bank::Irq => "irq",
            Bank::Svc => "svc",
            Bank::Abt => "abt",
            Bank::Und => "und",
            Bank::Mon => "mon",
            Bank::Hyp => "hyp",
        }
    }
}

impl fmt::Display for StatusRegMask {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.name())
    }
}

impl StatusRegMask {
    fn name(&self) -> &'static str {
        match self {
            StatusRegMask::CPSR_C => "cpsr_c",
            StatusRegMask::CPSR_X => "cpsr_x",
            StatusRegMask::CPSR_XC => "cpsr_xc",
            StatusRegMask::APSR_G => "apsr_g",
            StatusRegMask::CPSR_SC => "cpsr_sc",
            StatusRegMask::CPSR_SX => "cpsr_sx",
            StatusRegMask::CPSR_SXC => "cpsr_sxc",
            StatusRegMask::APSR_NZCV => "apsr_nzcv",
            StatusRegMask::APSR_NZCVQ => "apsr_nzcvq",
            StatusRegMask::CPSR_FC => "cpsr_fc",
            StatusRegMask::CPSR_FX => "cpsr_fx",
            StatusRegMask::CPSR_FXC => "cpsr_fxc",
            StatusRegMask::APSR_NZCVQG => "apsr_nzcvqg",
            StatusRegMask::CPSR_FSC => "cpsr_fsc",
            StatusRegMask::CPSR_FSX => "cpsr_fsx",
            StatusRegMask::CPSR_FSXC => "cpsr_fsxc",
            StatusRegMask::SPSR => "spsr",
            StatusRegMask::SPSR_C => "spsr_c",
            StatusRegMask::SPSR_X => "spsr_x",
            StatusRegMask::SPSR_XC => "spsr_xc",
            StatusRegMask::SPSR_S => "spsr_s",
            StatusRegMask::SPSR_SC => "spsr_sc",
            StatusRegMask::SPSR_SX => "spsr_sx",
            StatusRegMask::SPSR_SXC => "spsr_sxc",
            StatusRegMask::SPSR_F => "spsr_f",
            StatusRegMask::SPSR_FC => "spsr_fc",
            StatusRegMask::SPSR_FX => "spsr_fx",
            StatusRegMask::SPSR_FXC => "spsr_fxc",
            StatusRegMask::SPSR_FS => "spsr_fs",
            StatusRegMask::SPSR_FSC => "spsr_fsc",
            StatusRegMask::SPSR_FSX => "spsr_fsx",
            StatusRegMask::SPSR_FSXC => "spsr_fsxc",
        }
    }
}

#[allow(deprecated)]
impl <T: fmt::Write, Y: YaxColors> Colorize<T, Y> for super::Operand {
    fn colorize(&self, _colors: &Y, f: &mut T) -> fmt::Result {
        let mut f = yaxpeax_arch::display::FmtSink::new(f);
        let mut visitor = DisplayingOperandVisitor {
            f: &mut f,
        };
        self.visit(&mut visitor)
    }
}

impl super::Operand {
    fn visit<V: super::OperandVisitor>(&self, visitor: &mut V) -> Result<V::Ok, V::Error> {
        match *self {
            Operand::RegList(list) => {
                visitor.visit_reglist(list)
            }
            Operand::BankedReg(bank, reg) => {
                visitor.visit_banked_reg(bank, reg.number() as u16)
            },
            Operand::BankedSPSR(bank) => {
                visitor.visit_banked_spsr(bank)
            },
            Operand::Reg(reg) => {
                visitor.visit_reg(reg)
            }
            Operand::RegDeref(reg) => {
                visitor.visit_reg_deref(reg)
            }
            Operand::RegShift(shift) => {
                visitor.visit_reg_shift(shift)
            }
            Operand::RegDerefPostindexRegShift(reg, shift, add, wback) => {
                visitor.visit_reg_deref_postindex_reg_shift(reg, shift, add, wback)
            }
            Operand::RegDerefPreindexRegShift(reg, shift, add, wback) => {
                visitor.visit_reg_deref_preindex_reg_shift(reg, shift, add, wback)
            }
            Operand::RegDerefPostindexOffset(reg, offs, add, wback) => {
                visitor.visit_reg_deref_postindex_offset(reg, offs, add, wback)
            }
            Operand::RegDerefPreindexOffset(reg, offs, add, wback) => {
                visitor.visit_reg_deref_preindex_offset(reg, offs, add, wback)
            }
            Operand::RegDerefPostindexReg(reg, offsreg, add, wback) => {
                visitor.visit_reg_deref_postindex_reg(reg, offsreg, add, wback)
            }
            Operand::RegDerefPreindexReg(reg, offsreg, add, wback) => {
                visitor.visit_reg_deref_preindex_reg(reg, offsreg, add, wback)
            }
            Operand::Imm12(imm) => {
                visitor.visit_imm12(imm)
            }
            Operand::Imm32(imm) => {
                visitor.visit_imm32(imm)
            }
            Operand::BranchOffset(imm) => {
                visitor.visit_branch_offset(imm)
            }
            Operand::BranchThumbOffset(imm) => {
                visitor.visit_blx_offset(imm)
            }
            #[allow(deprecated)]
            Operand::Coprocessor(_num) => {
                unreachable!("Operand::Coprocessor is never constructed and will be removed in a future release");
            }
            Operand::CoprocOption(num) => {
                visitor.visit_coprocessor_option(num)
            }
            Operand::RegWBack(reg, wback) => {
                visitor.visit_reg_wback(reg, wback)
            }
            Operand::CReg(creg) => {
                visitor.visit_creg(creg)
            }
            Operand::StatusRegMask(mask) => {
                visitor.visit_status_reg_mask(mask)
            }
            Operand::Ror(amt) => {
                visitor.visit_rotate(amt)
            }
            Operand::APSR => {
                visitor.visit_apsr()
            },
            Operand::SPSR => {
                visitor.visit_spsr()
            },
            Operand::CPSR => {
                visitor.visit_cpsr()
            },
            Operand::Nothing => { panic!("tried to print Nothing operand") },
        }
    }
}

#[cfg(all(feature="alloc", feature="fmt"))]
mod buffer_sink {
    use core::fmt;
    use super::{InstructionDisplayer};

    // this exists to size `InstructionTextBuffer`'s buffer. it ideally would be somehow related to
    // `Arch`, but i'm not sure how to wire that up. so instead, calculate an appropriate max size
    // here.
    //
    // the longest instruction would be something like the longest mnemonic and four register
    // lists. in reality an ARM instruction has at most one register list so this is a gross
    // overestimate. but on with the show; assume 16 bytes for the longest mnemonic, then register
    // lists as `{(rNN, ){16}}`. each register list, then, is 80 bytes, brackets are two more, four
    // spaces for separation, and three commas for internal spacing. that's 16 + 320 + + 8 + 4 + 3.
    // round again and that gets you to 32 + 320 ~~ 352 bytes. out of sheer paranoia and excessive
    // padding desire, i'm going with 512 here as the next power of two.
    const MAX_INSTRUCTION_LEN: usize = 512;

    /// helper to format `armv7` instructions with highest throughput and least configuration. this is
    /// functionally a buffer for one armv7 instruction's text.
    ///
    /// ### when to use this over `fmt::Display`?
    ///
    /// `fmt::Display` is a fair choice in most cases. in some cases, `InstructionTextBuffer` may
    /// support formatting options that may be difficult to configure for a `Display` impl.
    /// additionally, `InstructionTextBuffer` may be able to specialize more effectively where
    /// `fmt::Display`, writing to a generic `fmt::Write`, may not.
    ///
    /// if your use case for `yaxpeax-arm` involves being bounded on the speed of disassembling and
    /// formatting instructions, `InstructionTextBuffer` may be a better choice.
    ///
    /// `InstructionTextBuffer` involves internal allocations; if your use case for `yaxpeax-arm`
    /// requires allocations never occurring, it is not an appropriate tool.
    ///
    /// ### example
    ///
    /// ```text
    /// use yaxpeax_arm::armv7::InstDecoder;
    /// use yaxpeax_arm::armv7::InstructionTextBuffer;
    ///
    /// let bytes = &[0x34, 0x78, 0xbf, 0xfd];
    /// let inst = InstDecoder::default().decode_slice(bytes).expect("can decode");
    /// let mut text_buf = InstructionTextBuffer::new();
    /// assert_eq!(
    ///     text_buf.format_inst(&inst).expect("can format"),
    ///     "ldc2 p8, c7, [pc, 0xd0]"
    /// );
    ///
    /// // or, getting the formatted instruction with `text_str`:
    /// assert_eq!(
    ///     text_buf.text_str(),
    ///     "ldc2 p8, c7, [pc, 0xd0]"
    /// );
    /// ```
    pub struct InstructionTextBuffer {
        content: alloc::string::String,
    }

    impl InstructionTextBuffer {
        /// create an `InstructionTextBuffer` with default settings. `InstructionTextBuffer`'s default
        /// settings format instructions identically to their corresponding `fmt::Display`.
        pub fn new() -> Self {
            let mut buf = alloc::string::String::new();
            buf.reserve(MAX_INSTRUCTION_LEN);
            Self {
                content: buf,
            }
        }

        /// format `inst` into this buffer. returns a borrow of that same internal buffer for convenience.
        ///
        /// this clears and reuses an internal buffer; if an instruction had been previously formatted
        /// through this buffer, it will be overwritten.
        pub fn format_inst<'buf, 'instr>(&'buf mut self, display: &InstructionDisplayer<'instr>) -> Result<&'buf str, fmt::Error> {
            // Safety: this sink is used to format exactly one instruction and then dropped. it can
            // never escape `format_inst`.
            let mut handle = unsafe { self.write_handle() };

            super::visit_inst(&display.instr, &mut handle)?;

            Ok(self.text_str())
        }

        /// return a borrow of the internal buffer. if an instruction has been formatted, the
        /// returned `&str` contains that instruction's buffered text.
        pub fn text_str(&self) -> &str {
            self.content.as_str()
        }

        /// do the necessary bookkeeping and provide an `InstructionTextSink` to write an instruction
        /// into.
        ///
        /// SAFETY: callers must print at most one instruction into this handle.
        unsafe fn write_handle(&mut self) -> yaxpeax_arch::display::InstructionTextSink {
            self.content.clear();
            // Safety: `content` was just cleared, so writing begins at the start of the buffer.
            // `content`is large enough to hold a fully-formatted instruction (see
            // `InstructionTextBuffer::new`).
            yaxpeax_arch::display::InstructionTextSink::new(&mut self.content)
        }
    }
}

#[cfg(all(feature="alloc", feature="fmt"))]
pub use buffer_sink::InstructionTextBuffer;
