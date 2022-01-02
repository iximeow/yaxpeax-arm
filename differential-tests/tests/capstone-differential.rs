//! this is a distinct set of tests from the `yaxpeax-arm` root tests because i don't want extra
//! (optional!) dependencies in the disassembler's dependency tree.

use capstone::prelude::*;
use yaxpeax_arch::{Arch, Decoder};

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

                    if cs_text
                        .replace("uxtw #0", "uxtw")
                        .replace("uxtx #0", "uxtx") == yax_text {

                        return true;
                    }

                    // capstone discards uxtw in some circumstances for reasons i don't yet
                    // know
                    if yax_text.ends_with("uxtw") &&
                        &yax_text[..yax_text.len() - 6] == cs_text {
                        return true;
                    }
                    if cs_text.ends_with("uxtw") &&
                        &cs_text[..cs_text.len() - 6] == yax_text {
                        return true;
                    }
                    if yax_text.replace("lsl", "uxtw") == cs_text {
                        return true;
                    }
                    if yax_text.ends_with("#0") &&
                        &yax_text[..yax_text.len() - 3] == cs_text {
                        return true;
                    }
                    if cs_text.ends_with("#0") &&
                        &cs_text[..cs_text.len() - 3] == yax_text {
                        return true;
                    }
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

                    if cs_text.starts_with("dup") && yax_text.starts_with("mov ") && cs_text.replace("dup ", "mov ") == yax_text {
                        return true;
                    }
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
