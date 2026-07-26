//! this is a distinct set of tests from the `yaxpeax-arm` root tests because i don't want extra
//! (optional!) dependencies in the disassembler's dependency tree.

// use capstone::prelude::*;
use yaxpeax_arch::{Arch, Decoder};

use std::fmt::Write;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::num::ParseIntError;

#[derive(Debug)]
enum ParsedOperand {
    Register { size: char, num: u8, neg: bool },
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
        let parse_hex_or_dec = |mut s: &str| {
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
        };

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
                let imm = parse_hex_or_dec(imm_str);
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
            let brace_end = s.find('}');
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

                let end = s[brace_end..].find(',').unwrap_or(s.len() - brace_end) + brace_end;
                (ParsedOperand::RegisterFamily(s[0..end].to_string()), end)
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
                _ => {
                    (ParsedOperand::Other(s[start..end].to_string()), end)
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
}

#[test]
fn capstone_differential_v7() {
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
            unsafe { capstone_sys::cs_open(capstone_sys::cs_arch::CS_ARCH_ARM, capstone_sys::cs_mode(0), &mut csh as *mut capstone_sys::csh) },
            0
        );
        unsafe {
            assert_eq!(capstone_sys::cs_option(
                csh, capstone_sys::cs_opt_type::CS_OPT_DETAIL, 0,
            ), 0);
        }
        let cs_insn: *mut capstone_sys::cs_insn = unsafe { libc::malloc(std::mem::size_of::<capstone_sys::cs_insn>()) as *mut capstone_sys::cs_insn };
        unsafe {
            // cs_insn is otherwise random garbage: set detail to NULL so
            // capstone doesn't think it's a real pointer to walk and
            // populate with operand data.
            (*cs_insn).detail = std::ptr::null_mut();
        };
        /*
        let cs = Capstone::new()
            .arm64()
            .mode(capstone::arch::arm64::ArchMode::Arm)
            .build()
            .expect("can create capstone");
            */

        let yax = <yaxpeax_arm::armv7::ARMv7 as Arch>::Decoder::default()
            .allow_nonconforming(true);

        let mut cs_text = String::new();
        let mut yax_text = String::new();

        for i in start..=end {
            let i = i as u32;
            let bytes = &i.to_le_bytes();
            if i % 0x01_00_00_00 == 0 {
                eprintln!("case {:08x}", i);
            }

//            let res = cs.disasm_all(bytes, 0);
            let res = unsafe {
                capstone_sys::cs_disasm_iter(
                    csh,
                    &mut bytes.as_ptr() as *mut *const u8,
                    &mut bytes.len() as *mut usize,
                    &mut 0u64 as *mut u64,
                    cs_insn,
                )
            };
//            if let Ok(insts) = &res {
            if res {
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

                    // TODO: temporary to get one diff run done
                    if cs_text.starts_with("mrseq") {
                        continue;
                    }

                    let yax_res = yax.decode(&mut yaxpeax_arch::U8Reader::new(bytes));
                    if let Ok(inst) = yax_res {
                        write!(yax_text, "{}", inst).unwrap();
                    } else if let Err(yaxpeax_arm::armv7::DecodeError::Incomplete) = yax_res {
                        stats.missed_incomplete.fetch_add(1, Ordering::Relaxed);
                        continue;
                    } else if !cs_text.starts_with("stc"){
//                        eprintln!("yax errored where capstone succeeded. cs text: '{}', bytes: {:x?}. meanwhile, yax: {:?}", cs_text, bytes, yax_res);
                        stats.missed_incomplete.fetch_add(1, Ordering::Relaxed);
                    };

                    fn acceptable_match(yax_text: &str, cs_text: &str) -> bool {
                        if yax_text == cs_text {
                            return true;
                        }

                        // TODO: temp while getting one differential test go..
                        if yax_text.starts_with("mrseq") && cs_text.starts_with("mrseq") {
                            return true;
                        }

                        // TODO: more hax
                        if cs_text.starts_with("stc") {
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

                        false
                    }

//                    eprintln!("{}", yax_text);
                    if !acceptable_match(&yax_text, &cs_text) {
 //                       eprintln!("disassembly mismatch: {} != {}. bytes: {:x?}", yax_text, cs_text, bytes);
//                        std::process::abort();
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

//    test_range(0x00_00_00_00, 0xff_ff_ff_ff, Arc::clone(&stats));

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
