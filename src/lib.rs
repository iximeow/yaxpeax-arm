//! # `yaxpeax-arm`, a decoder for `arm` instruction sets.
//!
//! `yaxpeax-arm` provides `armv7` (and below) decoders, including `thumb` support, as well a
//! decoder for `armv8`/`a64`.
//!
//! ## usage
//!
//! `yaxpeax-arm` is currently only usable through `yaxpeax-arch` traits:
//! ```
//! mod decoder {
//!     use yaxpeax_arch::{Arch, AddressDisplay, Decoder, Reader, ReaderBuilder};
//!
//!     pub fn decode_stream<
//!         'data,
//!         A: yaxpeax_arch::Arch,
//!         U: ReaderBuilder<A::Address, A::Word>,
//!     >(data: U) where
//!         A::Instruction: std::fmt::Display,
//!     {
//!         let mut reader = ReaderBuilder::read_from(data);
//!         let mut address: A::Address = reader.total_offset();
//!
//!         let decoder = A::Decoder::default();
//!         let mut decode_res = decoder.decode(&mut reader);
//!         loop {
//!             match decode_res {
//!                 Ok(ref inst) => {
//!                     println!("{}: {}", address.show(), inst);
//!                     decode_res = decoder.decode(&mut reader);
//!                     address = reader.total_offset();
//!                 }
//!                 Err(e) => {
//!                     println!("{}: decode error: {}", address.show(), e);
//!                     break;
//!                 }
//!             }
//!         }
//!     }
//! }
//!
//! use yaxpeax_arm::armv8::a64::Arch;
//! use yaxpeax_arch::{ReaderBuilder, U8Reader};
//! let data: &[u8] = &[0x94, 0x02, 0x1e, 0x32];
//! // would display `orr w20, w20, #0x4`.
//! decoder::decode_stream::<x86_64, _>(data);
//! ```

#![no_std]
#![deny(missing_docs)]

#[cfg(feature="use-serde")]
#[macro_use] extern crate serde_derive;
#[cfg(feature="use-serde")]
extern crate serde;
extern crate yaxpeax_arch;
extern crate bitvec;

/// `yaxpeax-arm`'s `ARMv7` decoder and `Arch` implementation.
pub mod armv7;
/// `yaxpeax-arm`'s `ARMv8` decoder and `Arch` implementation.
pub mod armv8;
