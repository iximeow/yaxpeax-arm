//! this is a distinct set of tests from the `yaxpeax-arm` root tests because i don't want extra
//! (optional!) dependencies in the disassembler's dependency tree.

use capstone::prelude::*;
use yaxpeax_arch::{Arch, Decoder};

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::num::ParseIntError;

#[derive(Debug)]
enum ParsedOperand {
    Register { size: char, num: u8 },
    Memory(String),
    MemoryWithOffset { base: String, offset: Option<i64>, writeback: bool },
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
            (Register { size: size_l, num: num_l }, Register { size: size_r, num: num_r }) => {
                size_l == size_r && num_l == num_r
            },
            (Memory(l), Memory(r)) => {
                l == r
            },
            (
                MemoryWithOffset { base: base_l, offset: offset_l, writeback: writeback_l },
                MemoryWithOffset { base: base_r, offset: offset_r, writeback: writeback_r },
            ) => {
                base_l == base_r &&
                offset_l == offset_r &&
                writeback_l == writeback_r
            },
            (Immediate(l), Immediate(r)) => {
                l == r
            },
            (PCRel(l), PCRel(r)) => {
                l == r
            },
            (Immediate(l), PCRel(r)) => {
                // assume pc=0 as capstone does by default
                *l == 0 + r
            },
            (PCRel(l), Immediate(r)) => {
                // assume pc=0 as capstone does by default
                0 + l == *r
            },
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
                // yax prints `asr #0` as just `asr`. is this actually a no-op?
                if (l == "asr" && r == "asr #0") || (l == "asr #0" && r == "asr") {
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
    assert_eq!(ParsedOperand::parse("xzr"), (ParsedOperand::Register { size: 'x', num: 0 }, 3));
    assert_eq!(ParsedOperand::parse("wzr"), (ParsedOperand::Register { size: 'w', num: 0 }, 3));
    assert_eq!(ParsedOperand::parse("w1"), (ParsedOperand::Register { size: 'w', num: 1 }, 2));
    assert_eq!(ParsedOperand::parse("x1"), (ParsedOperand::Register { size: 'x', num: 1 }, 2));
}

#[test]
fn test_instruction_parsing() {
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
}

impl ParsedOperand {
    fn parse(s: &str) -> (Self, usize) {
        let parse_hex_or_dec = |mut s: &str| {
            let mut negate = false;
            if s.as_bytes()[0] == b'-' {
                negate = true;
                s = &s[1..];
            }

            let v = if !s.starts_with("0x") {
                i64::from_str_radix(s, 10).expect("can parse string")
            } else {
                (u64::from_str_radix(&s[2..], 16).expect("can parse string") as i64)
            };
            if negate {
                -v
            } else {
                v
            }
        };

        let mut consumed = 0;
        if s.as_bytes()[0] == b'#' {
            let end = s.find(',').unwrap_or(s.len());
            let imm_str = &s[1..end];
            if imm_str.contains('.') {
                use std::str::FromStr;
                (ParsedOperand::Float(f64::from_str(imm_str).expect("can parse string")), end)
            } else {
                let imm = parse_hex_or_dec(imm_str);
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
            let imm = parse_hex_or_dec(imm_str);
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

            let offset = addr.rfind(',').map(|comma| {
                addr[comma + 1..].trim()
            }).and_then(|mut offset_str| {
                if offset_str.as_bytes().get(0) == Some(&b'#') {
                    offset_str = &offset_str[1..];

                    Some(parse_hex_or_dec(offset_str))
                } else {
                    None
                }
            });

            let base_end = addr.rfind(',').unwrap_or(addr.len());
            let base = addr[..base_end].trim();

            if writeback || offset.is_some() {
                (ParsedOperand::MemoryWithOffset {
                    base: base.to_string(),
                    offset: offset,
                    writeback,
                }, end)
            } else {
                (ParsedOperand::Memory(base.to_string()), end)
            }
        } else if s.as_bytes()[0] == b'{' {
            let mut brace_end = s.find('}');
            if let Some(brace_end) = brace_end {
                if s.as_bytes().get(brace_end + 1) == Some(&b'[') {
                    if let Some(end) = s.find(']') {
                        let group = &s[0..brace_end];
                        let lane = &s[brace_end + 2..end];
                        let lane = parse_hex_or_dec(lane);

                        return (ParsedOperand::SIMDElementLane {
                            elem: group.to_string(),
                            lane_selector: lane as u8,
                        }, end);
                    }
                }

                let end = s.find(',').unwrap_or(s.len());
                (ParsedOperand::RegisterFamily(s[0..end].to_string()), end)
            } else {
                let end = s.find(',').unwrap_or(s.len());
                (ParsedOperand::Other(s[0..end].to_string()), end)
            }
        } else {
            let mut end = s.find(',').unwrap_or(s.len());
            let substr = &s[..end];
            match (s.as_bytes()[0] as char) {
                sz @ 'w' | sz @ 'x' => {
                    if &s[1..end] == "zr" {
                        return (ParsedOperand::Register { size: sz, num: 0 }, 3);
                    }
                    let num: Result<u8, ParseIntError> = s[1..end].parse();
                    match num {
                        Ok(num) => {
                            (ParsedOperand::Register { size: sz, num }, end)
                        }
                        Err(e) => {
                            (ParsedOperand::Other(s[..end].to_string()), end)
                        }
                    }
                }
                sz @ 'b' | sz @ 'h' | sz @ 's' | sz @ 'd' | sz @ 'q' => {
                    let num: Result<u8, ParseIntError> = s[1..end].parse();
                    match num {
                        Ok(num) => {
                            (ParsedOperand::SIMDRegister { size: sz, num }, end)
                        }
                        Err(e) => {
                            (ParsedOperand::Other(s[..end].to_string()), end)
                        }
                    }
                }
                'v' => {
                    match substr.find('[') {
                        Some(lane_selector_start) => {
                            let lane_selector_end = substr.find(']').unwrap();
                            let elem = substr[..lane_selector_start].to_string();
                            let lane_selector = parse_hex_or_dec(&substr[lane_selector_start + 1..lane_selector_end]) as u8;
                            (ParsedOperand::SIMDElementLane { elem, lane_selector }, end)
                        }
                        None => {
                            // some kind of simd element that does not include a trailing `[]`.
                            // treat it as an opaque string for now.
                            (ParsedOperand::Other(substr.to_string()), end)
                        }
                    }
                }
                other => {
                    (ParsedOperand::Other(s[..end].to_string()), end)
                }
            }
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

            while operands_text.len() > 0 {
                if operands_text.as_bytes()[0] == b',' {
                    operands_text = &operands_text[1..];
                }
                operands_text = operands_text.trim();
                let (parsed, amount) = ParsedOperand::parse(&operands_text);
                operands[i] = Some(parsed);
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
}

#[test]
fn capstone_differential() {
    struct Stats {
        mismatch: AtomicUsize,
        good: AtomicUsize,
        yax_reject: AtomicUsize,
        missed_incomplete: AtomicUsize,
    }
    let mut yax_reject = AtomicUsize::new(0);
    let mut missed_incomplete = AtomicUsize::new(0);

    let stats = Stats {
        mismatch: AtomicUsize::new(0),
        good: AtomicUsize::new(0),
        yax_reject: AtomicUsize::new(0),
        missed_incomplete: AtomicUsize::new(0),
    };

    fn test_range(start: u64, end: u64, stats: Arc<Stats>) {
        let cs = Capstone::new()
            .arm64()
            .mode(capstone::arch::arm64::ArchMode::Arm)
            .build()
            .expect("can create capstone");

        let yax = <yaxpeax_arm::armv8::a64::ARMv8 as Arch>::Decoder::default();

        for i in start..=end {
            let i = i as u32;
            let bytes = &i.to_le_bytes();
            if i % 0x00_10_00_00 == 0 {
                eprintln!("case {:08x}", i);
            }

            let res = cs.disasm_all(bytes, 0);
            if let Ok(insts) = &res {
                let insts_slice = insts.as_ref();
                if insts_slice.len() == 1 {
                    // then yax should also succeed..
                    // and it should only be one instruction
                    let cs_text = format!("{}", insts_slice[0]);
                    let cs_text = &cs_text[5..];

                    let yax_res = yax.decode(&mut yaxpeax_arch::U8Reader::new(bytes));
                    let yax_text = if let Ok(inst) = yax_res {
                        format!("{}", inst)
                    } else if let Err(yaxpeax_arm::armv8::a64::DecodeError::IncompleteDecoder) = yax_res {
                        stats.missed_incomplete.fetch_add(1, Ordering::SeqCst);
                        continue;
                    } else {
                        // capstone dedodes the UNDEFINED encodings in C5.1.2 as "mrs", yax returns
                        // a decode error.
                        if cs_text.starts_with("mrs ") || cs_text.starts_with("msr ") {
                            stats.yax_reject.fetch_add(1, Ordering::SeqCst);
                            continue;
                        } else {
                            panic!("yax errored where capstone succeeded. cs text: '{}', bytes: {:x?}", cs_text, bytes);
                        }
                    };

                    fn acceptable_match(yax_text: &str, cs_text: &str) -> bool {
                        if yax_text == cs_text {
                            return true;
                        }

                        let parsed_yax = ParsedDisassembly::parse(yax_text);
                        let parsed_cs = ParsedDisassembly::parse(cs_text);

                        if parsed_yax == parsed_cs {
                            return true;
                        }

                        if false {
                            eprintln!("yax: {} -> {:?}", yax_text, parsed_yax);
                            eprintln!("cs: {} -> {:?}", cs_text, parsed_cs);
                        }

                        if parsed_yax.opcode == parsed_cs.opcode && parsed_yax.opcode == "mrs" && parsed_yax.operands[0] == parsed_cs.operands[0] {
                            if let Some(ParsedOperand::Other(o)) = parsed_yax.operands[1].as_ref() {
                                if o.starts_with("s") {
                                    // capstone knows about more system registers than yaxpeax-arm at the
                                    // moment, so this is likely a case where the disagreement is on the
                                    // name of the system register.
                                    return true;
                                }
                            }
                        }

                        if cs_text
                            .replace("uxtw #0", "uxtw")
                            .replace("uxtx #0", "uxtx") == yax_text {

                            return true;
                        }

                        // capstone discards uxtw in some circumstances for reasons i don't yet
                        // know
                        if let Some(yax_text) = yax_text.strip_suffix(", uxtw") {
                            if yax_text == cs_text {
                                return true;
                            }
                        }
                        if let Some(cs_text) = cs_text.strip_suffix(", uxtw") {
                            if yax_text == cs_text {
                                return true;
                            }
                        }

                        if yax_text.replace("lsl", "uxtw") == cs_text {
                            return true;
                        }

                        if cs_text.starts_with("ubfx ") {
                            return true;
                        }

                        // some instructions like `11400000` have an immeidate lsl #12 as their
                        // last operand. yax normalizes this to an unshifted `imm << 12`, capstone
                        // just prints lsl #12.
                        if cs_text.starts_with(yax_text) && cs_text.ends_with(", lsl #12") {
                            return true;
                        }

                        // yax and capstone deal with immediates in `mov reg, imm` a little
                        // differently. they're correct, but displayed differently (0xffffffff
                        // instead of -1)
                        if cs_text.starts_with("mov ") && yax_text.starts_with("mov ") {
                            return true;
                        }

                        // capstone just shows empty string for unrecognized prf{,u}m immediates,
                        // leaving broken text
                        if cs_text.starts_with("prfum ") && yax_text.starts_with("prfum ") {
                            return true;
                        }
                        if cs_text.starts_with("prfm ") && yax_text.starts_with("prfm ") {
                            return true;
                        }

                        // don't totally understand aliasing rules for `ORR (immediate)` and mov..
                        if cs_text.starts_with("mov ") && yax_text.starts_with("orr ") ||
                            cs_text.starts_with("orr ") && yax_text.starts_with("mov ")
                        {
                            return true;
                        }

                        // yax notmalizes movn to mov
                        if cs_text.starts_with("movn ") && yax_text.starts_with("mov ") {
                            return true;
                        }

                        // yax notmalizes movz to mov
                        if cs_text.starts_with("movz ") && yax_text.starts_with("mov ") {
                            return true;
                        }

                        if parsed_yax.opcode == "mov" && parsed_cs.opcode == "dup" {
                            if parsed_yax.operands == parsed_cs.operands {
                                return true;
                            }
                        }
    //                    if cs_text.starts_with("dup") && yax_text.starts_with("mov ") && cs_text.replace("dup ", "mov ") == yax_text {
    //                        return true;
    //                    }
                        // capstone bug! e0030033 is `bfxil w0, wzr, #0, #1`, but capstone picks
                        // the bfc alias instead. skip these, generally.
                        if yax_text.starts_with("bfxil") && (cs_text.starts_with("bfc") || cs_text.starts_with("bfi")) {
                            return true;
                        }

                        // yax omits `uxt{w,x}` for extended reg where extension matches the
                        // register size
                        if cs_text.starts_with(yax_text) && (cs_text.ends_with("uxtx") || cs_text.ends_with("uxtw")) {
                            return true;
                        }

                        // S being present or not has no bearing on the shift amount, #0 either
                        // way.
                        // yax will not print shift because of its ineffectual nature.
                        if (cs_text.starts_with("strb") || cs_text.starts_with("ldrb") || cs_text.starts_with("ldrsb") || cs_text.starts_with("ldr b") || cs_text.starts_with("str b")) && cs_text.contains(" lsl #0]") {
                            return true;
                        }

                        // yax uses lsl instead of uxtx when the reg size is uxtx. same for
                        // uxtw/w-regs
                        if cs_text.replace("uxtx", "lsl") == yax_text ||
                            cs_text.replace("uxtw", "lsl") == yax_text {
                            return true;
                        }

                        // yax shows dcps{1,2} operand, capstone does not?
                        if yax_text.starts_with("dcps") {
                            return true;
                        }

                        if cs_text.starts_with("msr ") {
                            return true;
                        }

                        // yax does not handle aliases for msr instructions yet
                        if yax_text.starts_with("msr ") {
                            return true;
                        }

                        // some kinda bug to deal with hint value width
                        if cs_text.starts_with("hint ") {
                            return true;
                        }
                        if cs_text.starts_with("dsb ") {
                            return true;
                        }
                        if cs_text.starts_with("clrex ") {
                            return true;
                        }
                        if yax_text.starts_with("sys ") {
                            return true;
                        }
                        if cs_text.starts_with("yield ") {
                            return true;
                        }
                        if cs_text.starts_with("wfe ") {
                            return true;
                        }
                        if cs_text.starts_with("wfi ") {
                            return true;
                        }
                        if cs_text.starts_with("sev ") {
                            return true;
                        }
                        if yax_text.starts_with("hint ") {
                            return true;
                        }

                        return false;
                    }

    //                eprintln!("{}", yax_text);
                    if !acceptable_match(&yax_text, cs_text) {
                        eprintln!("disassembly mismatch: {} != {}. bytes: {:x?}", yax_text, cs_text, bytes);
                        std::process::abort();
                    } else {
                        stats.good.fetch_add(1, Ordering::SeqCst);
                    }
                } else {
                    // yax should also fail?
                }
            }
        }
    }

    const NR_THREADS: u64 = 64;

    let range_size = (u32::MAX as u64 + 1) / NR_THREADS;

    let mut handles = Vec::new();

    let stats = Arc::new(stats);

    test_range(0x54_80_00_00, 0x54_80_00_10, Arc::clone(&stats));

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
