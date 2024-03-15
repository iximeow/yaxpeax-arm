//! this is a distinct set of tests from the `yaxpeax-arm` root tests because i don't want extra
//! (optional!) dependencies in the disassembler's dependency tree.

use capstone::prelude::*;
use yaxpeax_arch::{Arch, Decoder};

use std::num::ParseIntError;

#[derive(Debug)]
enum ParsedOperand {
    Register { size: char, num: u8 },
    Memory(String),
    SIMDRegister { size: char, num: u8 },
//    SIMDRegisterElements { num: u8, elems: u8, elem_size: char },
//    SIMDRegisterElement { num: u8, elem_size: char, elem: u8 },
    SIMDElementLane { elem: String, lane_selector: u8 },
    Immediate(i64),
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
            (Immediate(l), Immediate(r)) => {
                l == r
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
        } else if s.as_bytes()[0] == b'[' {
            let mut end = s.find(']').map(|x| x + 1).unwrap_or(s.len());
            if s.as_bytes().get(end) == Some(&b'!') {
                end += 1;
            }

            (ParsedOperand::Memory(s[0..end].to_string()), end)
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
    let cs = Capstone::new()
        .arm64()
        .mode(capstone::arch::arm64::ArchMode::Arm)
        .build()
        .expect("can create capstone");

    let yax = <yaxpeax_arm::armv8::a64::ARMv8 as Arch>::Decoder::default();

    let mut mismatch = 0;
    let mut good = 0;
    let mut yax_reject = 0;
    let mut missed_incomplete = 0;

    for i in 0x00_00_00_00..u32::MAX {
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
                    missed_incomplete += 1;
                    continue;
                } else {
                    panic!("yax errored where capstone succeeded. cs text: '{}', bytes: {:x?}", cs_text, bytes);
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

//                    eprintln!("yax: {} -> {:?}", yax_text, parsed_yax);
//                    eprintln!("cs: {} -> {:?}", cs_text, parsed_cs);

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
                    if let Some(yax_text) = yax_text.strip_suffix(" #0") {
                        if yax_text == cs_text {
                            return true;
                        }
                    }
                    if let Some(cs_text) = cs_text.strip_suffix(" #0") {
                        if yax_text == cs_text {
                            return true;
                        }
                    }
                    // TODO: what kind of cases is this for?
                    if cs_text.starts_with(yax_text) && cs_text.ends_with("000") {
                        return true;
                    };

                    if cs_text.starts_with("ubfx ") {
                        return true;
                    }

                    if yax_text.starts_with("adrp ") {
                        return true;
                    }

                    if yax_text.starts_with("adr ") {
                        return true;
                    }

                    if yax_text.starts_with("b ") {
                        return true;
                    }

                    if yax_text.starts_with("bl ") {
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

                    // differences on displaying immediates..
                    let new_cs_text = cs_text
                        .replace("#0x", "")
                        .replace("#-0x", "")
                        .replace("#-", "")
                        .replace("#", "");
                    let new_yax_text = yax_text
                        .replace("#0x", "")
                        .replace("#-0x", "")
                        .replace("#-", "")
                        .replace("#", "")
                        .replace("$+0x", "");
                    if new_cs_text == new_yax_text {
                        return true;
                    }

                    if cs_text.len() > 7 && yax_text.len() > 7 {
                        if &cs_text[..7] == &yax_text[..7] && (cs_text.contains("#-") || yax_text.contains("#-")) {
                            return true;
                        }
                        if &cs_text[..7] == &yax_text[..7] && (cs_text.contains("shll") || yax_text.contains("shll")) {
                            return true;
                        }
                    }
                    // capstone doesn't show relative offsets, always makes absolute for some
                    // ip
                    if yax_text.contains("$-0x") || yax_text.contains("$+0x") {
                        return true;
                    }

                    if yax_text.contains("esb") {
                        return true;
                    }

                    if yax_text.contains("movi") {
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

                    if cs_text.len() > 10 && yax_text.len() > 10 {
                        // eh they're probably the same but yax has a signed hex and capstone has
                        // unsigned
                        if &cs_text[..10] == &yax_text[..10] && cs_text.contains("ffffffff") && yax_text.contains("#-0x") {
                            return true;
                        }
                        // yax, for reg + shifted-reg operands, does not omit shift amount
                        if &cs_text[..10] == &yax_text[..10] && yax_text.contains(" #0x0]") {
                            return true;
                        }

                        // postindex offsets are base 10 in capstone sometimes?
                        if yax_text.contains("], #0x") && cs_text.contains("], #") &&
                            &cs_text[..20] == &yax_text[..20] {
                            return true;
                        }
                    }

                    // yax omits `uxt{w,x}` for extended reg where extension matches the
                    // register size
                    if cs_text.starts_with(yax_text) && (cs_text.ends_with("uxtx") || cs_text.ends_with("uxtw")) {
                        return true;
                    }

                    if cs_text.starts_with(yax_text) && cs_text.ends_with("0") {
                        return true;
                    }

                    // S being present or not has no bearing on the shift amount, #0 either
                    // way.
                    // yax will not print shift because of its ineffectual nature.
                    if (cs_text.starts_with("strb") || cs_text.starts_with("ldrb") || cs_text.starts_with("ldrsb") || cs_text.starts_with("ldr b") || cs_text.starts_with("str b")) && cs_text.contains(" lsl #0]") {
                        return true;
                    }

                    if cs_text == yax_text.replace(" #0", "") {
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
                    if cs_text.starts_with("mrs ") {
                        return true;
                    }
                    if cs_text.starts_with("sysl ") {
                        return true;
                    }
                    if yax_text.starts_with("hint ") {
                        return true;
                    }

                    if yax_text == &cs_text[..cs_text.len() - 1] && cs_text.ends_with(" ") {
                        return true;
                    }

                    return false;
                }

//                eprintln!("{}", yax_text);
                if !acceptable_match(&yax_text, cs_text) {
                    panic!("disassembly mismatch: {} != {}. bytes: {:x?}", yax_text, cs_text, bytes);
                } else {
                    good += 1;
                }
            } else {
                // yax should also fail?
            }
        }
    }
    eprintln!("match:      {}", good);
    eprintln!("mismatch:   {}", mismatch);
    eprintln!("bad reject: {}", yax_reject);
    eprintln!("incomplete: {}", missed_incomplete);
}
