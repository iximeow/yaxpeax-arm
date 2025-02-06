#![no_std]
#![no_main]

#[allow(unused_imports)]
use yaxpeax_arm;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[no_mangle]
pub extern "C" fn _start() -> ! { loop {} }
