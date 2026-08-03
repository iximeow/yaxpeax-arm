//! this is a distinct set of tests from the `yaxpeax-arm` root tests because i don't want extra
//! (optional!) dependencies in the disassembler's dependency tree.

// use capstone::prelude::*;
use yaxpeax_arch::{Arch, Decoder};

use std::fmt::Write;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::num::ParseIntError;

#[derive(Debug, PartialEq, Eq)]
enum MemOffset {
    Imm(i64),
    Shift { regnum: u8, rest: String },
    Reg { regnum: u8 },
}

#[derive(Debug)]
enum ParsedOperand {
    Register { size: char, num: u8, neg: bool },
    Memory(String),
    MemoryWithOffset { basereg: u8, offset: MemOffset, writeback: bool },
    SIMDRegister { size: char, num: u8 },
//    SIMDRegisterElements { num: u8, elems: u8, elem_size: char },
//    SIMDRegisterElement { num: u8, elem_size: char, elem: u8 },
    SIMDElementLane { elem: String, lane_selector: u8 },
    Immediate(i64),
    PCRel(i64),
    Float(f64),
    Other(String),
    RegisterFamily(String),
}

impl PartialEq for ParsedOperand {
    fn eq(&self, other: &Self) -> bool {
        use ParsedOperand::*;

        match (self, other) {
            (Register { size: size_l, num: num_l, neg: neg_l }, Register { size: size_r, num: num_r, neg: neg_r }) => {
                size_l == size_r && num_l == num_r && neg_l == neg_r
            },
            (Memory(l), Memory(r)) => {
                if l == "r10" && r == "sl" {
                    true
                } else {
                    l == r
                }
            },
            (
                MemoryWithOffset { basereg: base_l, offset: offset_l, writeback: writeback_l },
                MemoryWithOffset { basereg: base_r, offset: offset_r, writeback: writeback_r },
            ) => {
                (
                    base_l == base_r ||
                    offset_l == offset_r &&
                    writeback_l == writeback_r
                )
            },
            // smooth over yax printing `[rN]` rather than `[rN, #0]` like capstone.
            (Memory(l), MemoryWithOffset { basereg, offset: MemOffset::Imm(0), writeback: false }) => {
                if let Some(lreg) = ParsedOperand::parse_reg(l) {
                    lreg == *basereg
                } else {
                    false
                }
            },
            // and make equality reflexive.
            (MemoryWithOffset { basereg, offset: MemOffset::Imm(0), writeback: false }, Memory(r)) => {
                if let Some(rreg) = ParsedOperand::parse_reg(r) {
                    rreg == *basereg
                } else {
                    false
                }
            },
            (Immediate(l), Immediate(r)) => {
                l == r
            },
            (PCRel(l), PCRel(r)) => {
                l == r
            },
            // TODO: don't actually know if this is thumb, 32-bit thumb, arm, .. so try a few
            // things.
            (Immediate(l), PCRel(r)) => { *l == 2 + r || *l == 4 + r },
            (PCRel(l), Immediate(r)) => { 2 + l == *r || 4 + l == *r },

            (Float(l), Float(r)) => {
                l.to_ne_bytes() == r.to_ne_bytes()
            },
            (RegisterFamily(l), RegisterFamily(r)) => {
                l == r
            },
            (SIMDRegister { size: size_l, num: num_l }, SIMDRegister { size: size_r, num: num_r }) => {
                size_l == size_r && num_l == num_r
            },
            (SIMDElementLane { elem: elem_l, lane_selector: lane_l }, SIMDElementLane { elem: elem_r, lane_selector: lane_r }) => {
                elem_l == elem_r && lane_l == lane_r
            }
            (Other(l), Other(r)) => {
                if let (Some(left), Some(right)) = (l.strip_suffix(" r10"), r.strip_suffix(" sl")) {
                    // probably something like `lsl r10` vs `lsl sl`. so strip the registers off
                    // the end and compare the rest. notionally the registers should be parsed
                    // but..
                    left == right
                }
                // yax prints `asr #0` as just `asr`. is this actually a no-op?
                else if (l == "asr" && r == "asr #0") || (l == "asr #0" && r == "asr") {
                    true
                } else if (l == "lsr" && r == "lsr #0") || (l == "lsr #0" && r == "lsr") {
                    true
                } else if (l == "ror" && r == "ror #0") || (l == "ror #0" && r == "ror") {
                    true
                } else {
                    l == r
                }
            }
            (_, _) => {
                false
            }
        }
    }
}

#[test]
fn test_operand_parsing() {
    assert_eq!(ParsedOperand::parse("r3", 64), (ParsedOperand::Register { size: 'r', num: 3, neg: false }, 2));
    assert_eq!(ParsedOperand::parse("r11", 64), (ParsedOperand::Register { size: 'r', num: 11, neg: false }, 3));
    assert_eq!(ParsedOperand::parse("-r11", 64), (ParsedOperand::Register { size: 'r', num: 11, neg: true }, 4));
    assert_eq!(ParsedOperand::parse("sl", 32), (ParsedOperand::Register { size: 'r', num: 10, neg: false }, 2));
    assert_eq!(ParsedOperand::parse("-sl", 32), (ParsedOperand::Register { size: 'r', num: 10, neg: true }, 3));

    assert_eq!(
        ParsedOperand::parse("[r0, sl, lsl #3]", 32),
        (ParsedOperand::MemoryWithOffset { basereg: 0, offset: MemOffset::Shift { regnum: 10, rest: "lsl #3".to_string() }, writeback: false }, 16)
    );
    assert_eq!(
        ParsedOperand::parse("[r0, r10, lsl #3]", 32),
        (ParsedOperand::MemoryWithOffset { basereg: 0, offset: MemOffset::Shift { regnum: 10, rest: "lsl #3".to_string() }, writeback: false }, 17)
    );
}

#[test]
fn test_instruction_parsing() {
    /*
    let inst = ParsedDisassembly::parse("msub w17, w8, w15, w0");
    assert_eq!(inst, ParsedDisassembly {
        opcode: "msub".to_string(),
        operands: [
            Some(ParsedOperand::Register { size: 'w', num: 17 }),
            Some(ParsedOperand::Register { size: 'w', num: 8 }),
            Some(ParsedOperand::Register { size: 'w', num: 15 }),
            Some(ParsedOperand::Register { size: 'w', num: 0 }),
            None,
            None,
        ]
    });

    let inst = ParsedDisassembly::parse("stlurb w0, [x0, #0x1]");
    assert_eq!(inst, ParsedDisassembly {
        opcode: "stlurb".to_string(),
        operands: [
            Some(ParsedOperand::Register { size: 'w', num: 0 }),
            Some(ParsedOperand::MemoryWithOffset { base: "x0".to_string(), offset: Some(1), writeback: false }),
            None,
            None,
            None,
            None,
        ]
    });
    let inst2 = ParsedDisassembly::parse("stlurb w0, [x0, #1]");
    assert_eq!(inst, inst2);

    let inst = ParsedDisassembly::parse("mov wsp, #0x80000001");
    assert_eq!(inst.opcode, "mov");
    assert_eq!(inst.operands[0], Some(ParsedOperand::Register { size: 'w', num: 33 }));
    assert_eq!(inst.operands[1], Some(ParsedOperand::Immediate(-0x7fffffff)));
    */
}

impl ParsedOperand {
    fn parse(s: &str, width: u8) -> (Self, usize) {
        if s.as_bytes()[0] == b'#' {
            let end = s.find(',').unwrap_or(s.len());
            let mut imm_str = &s[1..end];
            // TODO: improve the following hack, useful to parse `[reg], -1!`
            if imm_str.ends_with('!') {
                imm_str = &s[1..end - 1];
            }
            if imm_str.contains('.') {
                use std::str::FromStr;
                (ParsedOperand::Float(f64::from_str(imm_str).expect("can parse string")), end)
            } else {
                let imm = ParsedOperand::parse_hex_or_dec(imm_str);
                let imm = if width == 32 {
                    imm as i32 as i64
                } else {
                    imm
                };
                (ParsedOperand::Immediate(imm), end)
            }
        } else if s.as_bytes()[0] == b'$' {
            let end = s.find(',').unwrap_or(s.len());
            let imm_str = &s[1..end];
            let imm_str = if imm_str.starts_with("+") {
                &imm_str[1..]
            } else {
                imm_str
            };
            let imm = ParsedOperand::parse_hex_or_dec(imm_str);
            (ParsedOperand::PCRel(imm), end)
        } else if s.as_bytes()[0] == b'[' {
            let brace_end = s.find(']').map(|x| x + 1).unwrap_or(s.len());
            let mut end = brace_end;
            let mut writeback = false;
            if s.as_bytes().get(end) == Some(&b'!') {
                end += 1;
                writeback = true;
            }

            let addr = &s[1..brace_end - 1];

            let offset = addr.find(',').map(|comma| {
                addr[comma + 1..].trim()
            }).map(|mut offset_str| {
                if let Some((reg, shift)) = ParsedOperand::parse_shift(offset_str) {
                    MemOffset::Shift { regnum: reg, rest: shift.to_string() }
                } else if let Some(reg) = ParsedOperand::parse_reg(offset_str) {
                    MemOffset::Reg { regnum: reg }
                } else {
                    MemOffset::Imm(ParsedOperand::parse_imm(offset_str))
                }
            });

            let base_end = addr.find(',').unwrap_or(addr.len());
            let base = addr[..base_end].trim();

            if let Some(offset) = offset {
                (ParsedOperand::MemoryWithOffset {
                    basereg: ParsedOperand::parse_reg(base).expect("base is reg"),
                    offset: offset,
                    writeback,
                }, end)
            } else if writeback {
                (ParsedOperand::MemoryWithOffset {
                    basereg: ParsedOperand::parse_reg(base).expect("base is reg"),
                    offset: MemOffset::Imm(0),
                    writeback,
                }, end)
            } else {
                (ParsedOperand::Memory(base.to_string()), end)
            }
        } else if s.as_bytes()[0] == b'{' {
            let brace_end = s.find('}');
            if let Some(brace_end) = brace_end {
                if s.as_bytes().get(brace_end + 1) == Some(&b'[') {
                    if let Some(end) = s.find(']') {
                        let group = &s[0..brace_end];
                        let lane = &s[brace_end + 2..end];
                        let lane = ParsedOperand::parse_hex_or_dec(lane);

                        return (ParsedOperand::SIMDElementLane {
                            elem: group.to_string(),
                            lane_selector: lane as u8,
                        }, end);
                    }
                }

                let end = s[brace_end..].find(',').unwrap_or(s.len() - brace_end) + brace_end;
                let regs = s[0..end].to_string();
                // TODO: parse register numbers more reasonably...
                (ParsedOperand::RegisterFamily(regs.replace("sl", "r10")), end)
            } else {
                let end = s.find(',').unwrap_or(s.len());
                (ParsedOperand::Other(s[0..end].to_string()), end)
            }
        } else {
            let mut start = 0;
            let end = s.find(',').unwrap_or(s.len());
            let mut substr = &s[..end];
            let mut neg = false;
            if substr.as_bytes()[0] == b'-' {
                start += 1;
                neg = true;
                substr = &substr[1..];
            }
            if substr == "sl" {
                return (ParsedOperand::Register { size: 'r', num: 10, neg }, end);
            }
            match s.as_bytes()[start] as char {
                sz @ 'r' => {
                    if &s[start + 1..end] == "zr" {
                        return (ParsedOperand::Register { size: sz, num: 32, neg }, end);
                    }
                    if &s[start + 1..end] == "sp" {
                        return (ParsedOperand::Register { size: sz, num: 33, neg }, end);
                    }
                    let num: Result<u8, ParseIntError> = s[start + 1..end].parse();
                    match num {
                        Ok(num) => {
                            (ParsedOperand::Register { size: sz, num, neg }, end)
                        }
                        Err(_) => {
                            (ParsedOperand::Other(s[start..end].to_string()), end)
                        }
                    }
                }
                sz @ 'b' | sz @ 'h' | sz @ 's' | sz @ 'd' | sz @ 'q' => {
                    let num: Result<u8, ParseIntError> = s[start + 1..end].parse();
                    match num {
                        Ok(num) => {
                            (ParsedOperand::SIMDRegister { size: sz, num }, end)
                        }
                        Err(_) => {
                            (ParsedOperand::Other(s[start..end].to_string()), end)
                        }
                    }
                }
                'v' => {
                    match substr.find('[') {
                        Some(lane_selector_start) => {
                            let lane_selector_end = substr.find(']').unwrap();
                            let elem = substr[..lane_selector_start].to_string();
                            let lane_selector = ParsedOperand::parse_hex_or_dec(&substr[lane_selector_start + 1..lane_selector_end]) as u8;
                            (ParsedOperand::SIMDElementLane { elem, lane_selector }, end)
                        }
                        None => {
                            // some kind of simd element that does not include a trailing `[]`.
                            // treat it as an opaque string for now.
                            (ParsedOperand::Other(substr.to_string()), end)
                        }
                    }
                }
                _ => {
                    (ParsedOperand::Other(s[start..end].to_string()), end)
                }
            }
        }
    }

    fn parse_hex_or_dec(mut s: &str) -> i64 {
        let mut negate = false;
        if s.as_bytes()[0] == b'-' {
            negate = true;
            s = &s[1..];
        }

        let v = if !s.starts_with("0x") {
            i64::from_str_radix(s, 10).map_err(|e| { panic!("failed to parse {}", s); }).expect("can parse string")
        } else {
            u64::from_str_radix(&s[2..], 16).expect("can parse string") as i64
        };
        if negate {
            -v
        } else {
            v
        }
    }

    fn parse_imm(mut s: &str) -> i64 {
        if s.starts_with("#") {
            ParsedOperand::parse_hex_or_dec(&s[1..])
        } else {
            ParsedOperand::parse_hex_or_dec(s)
        }
    }

    fn parse_reg(s: &str) -> Option<u8> {
        if s.starts_with("r") {
            Some(s[1..].parse().expect("can parse regnum"))
        } else {
            match s {
                "sb" => Some(9),
                "sl" => Some(10),
                "fp" => Some(11),
                "ip" => Some(12),
                "sp" => Some(13),
                "lr" => Some(14),
                "pc" => Some(15),
                _ => {
                    None
                }
            }
        }
    }

    fn parse_shift(s: &str) -> Option<(u8, &str)> {
        if let Some(comma) = s.find(",") {
            let reg = s[..comma].trim();
            let rest = s[comma + 1..].trim();
            assert!(
                rest.starts_with("lsl") ||
                   rest.starts_with("lsr") ||
                   rest.starts_with("asr") ||
                   rest.starts_with("ror"));
            let regnum = ParsedOperand::parse_reg(reg).unwrap_or_else(|| {
                panic!("shift base should be reg, was not in: {}", s);
            });
            Some((regnum, rest))
        } else {
            None
        }
    }
}

#[derive(Debug, PartialEq)]
struct ParsedDisassembly {
    opcode: String,
    // arm instructions do not have six operands, but due to parse ambiguity and the rather hackjob
    // parser here, pretend they might.
    operands: [Option<ParsedOperand>; 6]
}

impl ParsedDisassembly {
    fn parse(s: &str) -> Self {
        let mut operands = [None, None, None, None, None, None];
        if let Some((opcode, mut operands_text)) = s.split_once(' ') {
            let opcode = opcode.to_string();

            let mut i = 0;
            let mut width = 64;

            while operands_text.len() > 0 {
                if operands_text.as_bytes()[0] == b',' {
                    operands_text = &operands_text[1..];
                }
                operands_text = operands_text.trim();
                let (parsed, amount) = ParsedOperand::parse(&operands_text, width);
                operands[i] = Some(parsed);
                if let Some(ParsedOperand::Register { size: 'w', .. }) = &operands[i] {
                    width = 32;
                }
                operands_text = &operands_text[amount..];
                i += 1;
            }

            ParsedDisassembly {
                opcode,
                operands,
            }
        } else {
            ParsedDisassembly {
                opcode: s.to_string(),
                operands,
            }
        }
    }

    fn operand_count(&self) -> u8 {
        let mut i = 0;

        for op in self.operands.iter() {
            if op.is_none() {
                break;
            }
            i += 1;
        }

        i
    }
}

#[test]
fn capstone_differential_thumb() {
    struct Stats {
        mismatch: AtomicUsize,
        good: AtomicUsize,
        yax_reject: AtomicUsize,
        missed_incomplete: AtomicUsize,
    }

    let stats = Stats {
        mismatch: AtomicUsize::new(0),
        good: AtomicUsize::new(0),
        yax_reject: AtomicUsize::new(0),
        missed_incomplete: AtomicUsize::new(0),
    };

    fn test_range(start: u64, end: u64, stats: Arc<Stats>) {
        /*
        let mut local_mismatch = 0usize;
        let mut local_good = 0usize;
        let mut local_yax_reject = 0usize;
        let mut local_missed_incomplete = 0usize;
        */

        let mut csh: capstone_sys::csh = capstone_sys::csh::default();
        assert_eq!(
            unsafe { capstone_sys::cs_open(capstone_sys::cs_arch::CS_ARCH_ARM, capstone_sys::cs_mode(1<<4), &mut csh as *mut capstone_sys::csh) },
            0
        );
        unsafe {
            assert_eq!(capstone_sys::cs_option(
                csh, capstone_sys::cs_opt_type::CS_OPT_DETAIL, 0,
            ), 0);
        }
        let mut cs_insn: *mut capstone_sys::cs_insn = std::ptr::null_mut();
        /*
        let cs = Capstone::new()
            .arm64()
            .mode(capstone::arch::arm64::ArchMode::Arm)
            .build()
            .expect("can create capstone");
            */

        let yax = <yaxpeax_arm::armv7::ARMv7 as Arch>::Decoder::default()
            .with_thumb_mode(true)
            .allow_nonconforming(true);

        let mut cs_text = String::new();
        let mut yax_text = String::new();

        for i in start..=end {
            let i = i as u32;
            let bytes = &i.to_le_bytes();
            if i % 0x01_00_00_00 == 0 {
//                eprintln!("case {:08x}", i);
            }

            if cs_insn != std::ptr::null_mut() {
                unsafe {
                    capstone_sys::cs_free(cs_insn, 1);
                    cs_insn = std::ptr::null_mut();
                }
            }

            let res = unsafe {
                capstone_sys::cs_disasm(
                    csh,
                    bytes.as_ptr() as *const u8,
                    bytes.len() as usize,
                    0u64, // address
                    1,    // max decoded instrs
                    &mut cs_insn,
                )
            };
//            if let Ok(insts) = &res {
            if res != 0 {
//                let insts_slice = insts.as_ref();
//              if insts_slice.len() == 1 {
                {
                    cs_text.clear();
                    yax_text.clear();
                    // then yax should also succeed..
                    // and it should only be one instruction
//                    let cs_text = format!("{}", insts_slice[0]);
//                    let cs_text = &cs_text[5..];
                    unsafe {
                        use std::ffi::CStr;
                        write!(cs_text, "{} {}",
                            CStr::from_ptr((*cs_insn).mnemonic.as_ptr()).to_str().unwrap(),
                            CStr::from_ptr((*cs_insn).op_str.as_ptr()).to_str().unwrap(),
                        ).unwrap();
                    };

                    let yax_res = yax.decode(&mut yaxpeax_arch::U8Reader::new(bytes));
                    if let Ok(inst) = yax_res {
                        write!(yax_text, "{}", inst).unwrap();
                    } else if let Err(yaxpeax_arm::armv7::DecodeError::Incomplete) = yax_res {
                        stats.missed_incomplete.fetch_add(1, Ordering::Relaxed);
                        continue;
                    } else {
                        let word = i;
                        if (word >> 16) & 0xf0ff == 0xf0bf &&
                            cs_text.starts_with("it") &&
                            yax_res == Err(yaxpeax_arm::armv7::DecodeError::Nonconforming) {
                            // capstone accepts IT/firstcond=1111, but the encoding is
                            // UNPREDICTABLE.
                            continue;
                        } else if cs_text.starts_with("udf") &&
                            yax_res == Err(yaxpeax_arm::armv7::DecodeError::Undefined) {
                            // TODO: yax decodes undefined instructions as "Undefined", but the
                            // manual reports them as udf #imm. yax needs to change.
                            continue;
                        } else if yax_res == Err(yaxpeax_arm::armv7::DecodeError::Unpredictable) {
                            // TODO: some better way of verifying unpredictable encodings.
                            continue;
                        } else if cs_text.starts_with("stlex" ) || cs_text.starts_with("ldrex") {
                            // TODO: yax is missing thumb-mode ldrexd/stlexd? it's not clear which
                            // ISA version these were added in, though they're in DDI0487 G.b ..
                            continue;
                        } else if cs_text.starts_with("usada8") || cs_text.starts_with("usad8") {
                            // TODO: not sure what's up with this. fix it!
                            continue;
                        } else if !cs_text.starts_with("stc") {
                            eprintln!("yax errored where capstone succeeded. cs text: '{}', bytes: {:x?}. meanwhile, yax: {:?}", cs_text, bytes, yax_res);
                            stats.missed_incomplete.fetch_add(1, Ordering::Relaxed);
                            continue;
                        };
                    }

                    fn acceptable_match(word: u32, yax_text: &str, cs_text: &str) -> bool {
                        if yax_text == cs_text {
                            return true;
                        }

                        // TODO: capstone prints `blx #0x...`, yax prints `blx.w $+0x...`
                        if yax_text.starts_with("blx.w ") && cs_text.starts_with("blx ") {
                            return true;
                        }

                        // TODO: capstone prints `bl #0x...`, yax prints `bl.w $+0x...`
                        if yax_text.starts_with("bl.w ") && cs_text.starts_with("bl ") {
                            return true;
                        }

                        if yax_text == "udf #0xfe" && cs_text == "trap " {
                            // TODO:
                            return true;
                        }

                        let parsed_yax = ParsedDisassembly::parse(yax_text);
                        let parsed_cs = ParsedDisassembly::parse(cs_text);

                        if parsed_yax == parsed_cs {
                            return true;
                        }

                        // yax shows the alias out of the box, capstone undoes it:
                        // > pop.w {sb} != ldm.w sp!, {sb}. bytes: [bd, e8, 0, 2]
                        if parsed_yax.opcode == "pop.w" && parsed_cs.opcode == "ldm.w" && parsed_yax.operands[0] == parsed_cs.operands[1] {
                            return true;
                        }

                        // yax shows the alias out of the box, capstone undoes it:
                        // > push {sb} != stmdb sp!, {sb}. bytes: [2d, e9, 0, 2]
                        if parsed_yax.opcode == "push" && parsed_cs.opcode == "stmdb" && parsed_yax.operands[0] == parsed_cs.operands[1] {
                            return true;
                        }

                        // more aliasing defaults..
                        // > push.w {r1} != str r1, [sp, #-0x4]!. bytes: [4d, f8, 4, 1d]
                        if parsed_yax.opcode == "push.w" && parsed_cs.opcode == "str" {
                            return true;
                        }

                        if (parsed_yax.opcode == "add" &&
                            parsed_cs.opcode == "add") ||
                            (parsed_yax.opcode == "adds" &&
                             parsed_cs.opcode == "adds") {
                            // capstone prints the T2 encoding of `ADD (register, Thumb)` as if
                            // it is the T1 encoding with three registers.
                            if parsed_yax.operand_count() == 2 && parsed_cs.operand_count() == 3 {
                                if parsed_yax.operands[0] == parsed_cs.operands[0] &&
                                    parsed_yax.operands[1] == parsed_cs.operands[1] &&
                                    parsed_cs.operands[0] == parsed_cs.operands[2] {
                                    return true;
                                }
                            }

                            // capstone prints the T2 encoding of `ADD (SP plus immediate)` with
                            // two operands instead of the three from the manual.
                            if word & 0xff80 == 0xb000 &&
                                parsed_yax.opcode == "add" &&
                                parsed_cs.opcode == "add" &&
                                parsed_yax.operands[0] == parsed_cs.operands[0] &&
                                parsed_yax.operands[0] == parsed_yax.operands[1] &&
                                parsed_cs.operands[1] == parsed_yax.operands[2] {
                                return true;
                            }
                        }

                        if (parsed_yax.opcode == "sub" &&
                            parsed_cs.opcode == "sub") {
                            // capstone prints the T1 encoding of `SUB (SP minus immediate)` with
                            // two operands instead of the three from the manual.
                            if word & 0xff80 == 0xb080 &&
                                parsed_yax.opcode == "sub" &&
                                parsed_cs.opcode == "sub" &&
                                parsed_yax.operands[0] == parsed_cs.operands[0] &&
                                parsed_yax.operands[0] == parsed_yax.operands[1] &&
                                parsed_cs.operands[1] == parsed_yax.operands[2] {
                                return true;
                            }
                        }

                        // TODO: yaxpeax-arm doesn't know about armv8-m yet, which gets `bxns` to
                        // replace `bx` in some encodings.
                        if parsed_yax.opcode == "bx" && parsed_cs.opcode == "bxns" {
                            if parsed_yax.operands == parsed_cs.operands {
                                return true;
                            }
                        }

                        // TODO: same for blx/blxns.
                        if parsed_yax.opcode == "blx" && parsed_cs.opcode == "blxns" {
                            if parsed_yax.operands == parsed_cs.operands {
                                return true;
                            }
                        }

                        if parsed_yax.operands == parsed_cs.operands {
                            // TODO: yax probably should simply write `stm` in this case like the
                            // manual implies and capstone does.
                            if parsed_yax.opcode == "stmia" && parsed_cs.opcode == "stm" {
                                    return true;
                            }

                            // TODO: what???
                            // > stmia r0!, {r0} != stmgt r0!, {r0}. bytes: [1, c0, 92, 1f]
                            if parsed_yax.opcode == "stmia" && parsed_cs.opcode == "stmgt" {
                                    return true;
                            }

                            // TODO: yax says .w when it doesn't need to, allegedly?
                            // TODO: also omits a w when capstone adds one? (mov vs movw: "mov sp, #0x1183 != movw sp, #0x1183. bytes: [41, f2, 83, 1d]")
                            if parsed_yax.opcode == format!("{}{}", parsed_cs.opcode, ".w") || parsed_yax.opcode.clone() + "w" == parsed_cs.opcode {
                                return true;
                            }

                            if parsed_yax.opcode.replace(".w", "w") == parsed_cs.opcode {
                                // TODO: yax prints wide sub-immediate/add-immediate as `sub.w`, capstone
                                // says `subw` (same for add). this probably could use fixing.
                                // comparisons:
                                // > sub.w r4, r4, #0x483 != subw r4, r4, #0x483. bytes: [a4, f2, 83, 44]
                                // > add.w r10, r1, #0x985 != addw sl, r1, #0x985. bytes: [1, f6, 85, 1a]
                                // > pld.w pc, [fp, #0xf04] != pldw [fp, #0xf04]. bytes: [bb, f8, 4, ff]
                                return true;
                            }

                            // TODO: so many signed multiply-related mishaps (usually around the
                            // M/R bits.
                            if parsed_yax.opcode.starts_with("sm") && parsed_cs.opcode.starts_with("sm") {
                                return true;
                            }
                        }

                        // TODO: a weirder mishap with smmls{r}
                        // > smmls.w pc, r3, lr != smmlsr pc, r3, lr, pc. bytes: [63, fb, 1e, ff]
                        if parsed_yax.opcode.starts_with("smmls.w") && parsed_cs.opcode.starts_with("smmlsr") {
                            return true;
                        }

                        if parsed_yax.opcode == parsed_cs.opcode {
                            let mut last_operand = 0;
                            for op in parsed_yax.operands.iter() {
                                if op.is_none() {
                                    break;
                                }

                                last_operand += 1;
                            }
                            if parsed_yax.operands[..last_operand] == parsed_cs.operands[..last_operand] &&
                                parsed_cs.operands[last_operand] == Some(ParsedOperand::Immediate(0)) {
                                return true;
                            }
                        }

                        if parsed_yax.opcode.replace(".w", "") == parsed_cs.opcode.replace(".w", "") {
                            // TODO: yax prints garbage like `b.wgt` instead of `bgt.w`. yikes.
                            return true;
                        }

                        static BRANCHES: &'static [&'static str] = &[
                            "bgt", "bhi", "b", "ble", "bge", "blt", "bge",
                            "bhs", "blo", "beq", "bne", "bpl", "bmi", "bvc",
                            "bvs", "bls", "bfi", "b.w","blx.w",
                        ];
                        if BRANCHES.contains(&parsed_yax.opcode.as_str()) && parsed_yax.opcode == parsed_cs.opcode {
                            // TODO: the harness doesn't relativeizie branch targets?
                            return true;
                        }

                        if false {
                            eprintln!("parsed yax: {:?}", parsed_yax);
                            eprintln!("parsed cs: {:?}", parsed_cs);
                            eprintln!("yax: {} -> {:?}", yax_text, parsed_yax);
                            eprintln!("cs: {} -> {:?}", cs_text, parsed_cs);
                        }

                        false
                    }

//                    eprintln!("{}", yax_text);
                    if !acceptable_match(i, &yax_text, &cs_text) {
                        eprintln!("disassembly mismatch: {} != {}. bytes: {:x?}", yax_text, cs_text, bytes);
//                        std::process::abort();
                        stats.mismatch.fetch_add(1, Ordering::Relaxed);
                    } else {
                        stats.good.fetch_add(1, Ordering::Relaxed);
                    }
//                } else {
                    // yax should also fail?
                }
            }
        }

        // add to stats only once because for some reason on aarch64 the increments here call into
        // a builtin to conditionally use the armv8.1 atomic instructions....???
        /*
        stats.mismatch.fetch_add(local_mismatch, Ordering::Release);
        stats.good.fetch_add(local_good, Ordering::Release);
        stats.yax_reject.fetch_add(local_yax_reject, Ordering::Release);
        stats.missed_incomplete.fetch_add(local_missed_incomplete, Ordering::Release);
        */
    }

    const NR_THREADS: u64 = 512;

    let range_size = (u32::MAX as u64 + 1) / NR_THREADS;

    let mut handles = Vec::new();

    let stats = Arc::new(stats);

    // test_range(0x00_00_00_00, 0xff_ff_ff_ff, Arc::clone(&stats));

    for i in 0..NR_THREADS {
        let stats = Arc::clone(&stats);
        let handle = std::thread::spawn(move || test_range(i * range_size, i * range_size + range_size, stats));
        handles.push(handle);
    }

    while let Some(handle) = handles.pop() {
        handle.join().unwrap();
    }

    eprintln!("match:      {}", stats.good.load(Ordering::SeqCst));
    eprintln!("mismatch:   {}", stats.mismatch.load(Ordering::SeqCst));
    eprintln!("bad reject: {}", stats.yax_reject.load(Ordering::SeqCst));
    eprintln!("incomplete: {}", stats.missed_incomplete.load(Ordering::SeqCst));
}
