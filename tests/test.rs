// #![feature(test)]
//
// extern crate test;

mod armv7;
mod armv8;

use yaxpeax_arch::{Arch, Decoder, U8Reader};
use std::fmt::Write;

fn test_range<A: Arch>(decoder: &A::Decoder, start: u64, end: u64)
where
    for <'a> U8Reader<'a>: yaxpeax_arch::Reader<<A as Arch>::Address, <A as Arch>::Word>,
    <A as Arch>::Instruction: std::fmt::Display
{

    let mut instr = A::Instruction::default();
    let mut s = String::new();

    for i in start..=end {
        if i & 0x01_ff_ff_ff == 0 {
            eprintln!("case {:08x}", i);
        }
        let i = i as u32;
        let bytes = i.to_le_bytes();
        let res = decoder.decode_into(&mut instr, &mut U8Reader::new(&bytes));
        if let Ok(()) = res {
            s.clear();
            write!(s, "{}", instr).unwrap();
        }
    }
}

fn par_test_u32(test_range: fn(u64, u64)) {
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

#[test]
#[ignore]
fn test_armv7_does_not_panic() {
    par_test_u32(|start, end| {
        let armv7 = <yaxpeax_arm::armv7::ARMv7 as Arch>::Decoder::default();

        test_range::<yaxpeax_arm::armv7::ARMv7>(&armv7, start, end);
    });
}
#[test]
#[ignore]
fn test_armv7_thumb_does_not_panic() {
    par_test_u32(|start, end| {
        let mut armv7_t = <yaxpeax_arm::armv7::ARMv7 as Arch>::Decoder::default();
        armv7_t.set_thumb_mode(true);

        test_range::<yaxpeax_arm::armv7::ARMv7>(&armv7_t, start, end);
    });
}

#[test]
#[ignore]
fn test_armv8_does_not_panic() {
    par_test_u32(|start, end| {
        let armv8 = <yaxpeax_arm::armv8::a64::ARMv8 as Arch>::Decoder::default();

        test_range::<yaxpeax_arm::armv8::a64::ARMv8>(&armv8, start, end);
    });
}
