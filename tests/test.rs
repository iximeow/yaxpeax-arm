// #![feature(test)]
//
// extern crate test;

mod armv7;
mod armv8;

use yaxpeax_arch::{Arch, Decoder, U8Reader};
use std::fmt::Write;

#[test]
#[ignore]
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
#[ignore]
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
#[ignore]
fn test_armv8_does_not_panic() {
    fn test_range(start: u64, end: u64) {
        let armv8 = <yaxpeax_arm::armv8::a64::ARMv8 as Arch>::Decoder::default();

        let mut instr = <yaxpeax_arm::armv8::a64::ARMv8 as yaxpeax_arch::Arch>::Instruction::default();
        let mut s = String::new();

        for i in start..=end {
            if i & 0x01_ff_ff_ff == 0 {
                eprintln!("case {:08x}", i);
            }
            let i = i as u32;
            let bytes = i.to_le_bytes();
            let res = armv8.decode_into(&mut instr, &mut U8Reader::new(&bytes));
            if let Ok(()) = res {
                s.clear();
                write!(s, "{}", instr).unwrap();
            }
        }
    }

    const NR_THREADS: u64 = 512;

    const RANGE_SIZE: u64 = (u32::MAX as u64 + 1) / NR_THREADS;

    let mut handles = Vec::new();

    for i in 0..NR_THREADS {
        let handle = std::thread::spawn(move || test_range(i * RANGE_SIZE, (i + 1) * RANGE_SIZE));
        handles.push(handle);
    }

    while let Some(handle) = handles.pop() {
        handle.join().unwrap();
    }
}
