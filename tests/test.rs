// #![feature(test)]
//
// extern crate test;

mod armv7;
mod armv8;

use yaxpeax_arch::{Arch, Decoder, U8Reader};

#[test]
fn test_armv7_does_not_panic() {
    let armv7 = <yaxpeax_arm::armv7::ARMv7 as Arch>::Decoder::default();

    for i in 0..=u32::MAX {
        let bytes = i.to_le_bytes();
        let res = armv7.decode(&mut U8Reader::new(&bytes));
        if let Ok(instr) = res {
            let s = instr.to_string();
            drop(s);
        }
    }
}
#[test]
fn test_armv7_thumb_does_not_panic() {
    let mut armv7_t = <yaxpeax_arm::armv7::ARMv7 as Arch>::Decoder::default();
    armv7_t.set_thumb_mode(true);

    for i in 0..=u32::MAX {
        let bytes = i.to_le_bytes();
        let res = armv7_t.decode(&mut U8Reader::new(&bytes));
        if let Ok(instr) = res {
            let s = instr.to_string();
            drop(s);
        }
    }
}
#[test]
fn test_armv8_does_not_panic() {
    let armv8 = <yaxpeax_arm::armv8::a64::ARMv8 as Arch>::Decoder::default();

    for i in 0..=u32::MAX {
        let bytes = i.to_le_bytes();
        let res = armv8.decode(&mut U8Reader::new(&bytes));
        if let Ok(instr) = res {
            let s = instr.to_string();
            drop(s);
        }
    }
}
