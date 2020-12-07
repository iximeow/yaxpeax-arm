## yaxpeax-arm

`yaxpeax-arm` provides implementations of decoders for the armv7, v7/thumb, v7/thumb2, and aarch64/a64 instruction sets.

the entrypoint to begin decoding is either `armv7::InstDecoder` (`ARMv7::Decoder::default()`) or `armv8::InstDecoder` (`ARMv8::Decoder::default()`). `default` for both decoders is to decode in ARM mode. `default` will try to decode as permissively as possible, even attempting to produce some kind of instruction for `UNPREDICTABLE` patterns, where possible. for armv7 and below, `default_thumb` produces a similarly permissive set of rules, but for decoding thumb/thumb2 instructions.

ARMv7 and thumb mode instructions decode to the same structure: `armv7::Instruction`. this is not known to introduce ambiguities, and if you must discern thumb vs non-thumb origins, `armv7::Instruction::thumb` will reflect the decoder state when decoding the instruction of interest. additionally, `armv7::Instruction::w` reports if the instruction was a wide (32-bit) thum instruction.

for all ARMv7 instructions, `armv7::Instruction::s()` reports if the instruction will update status flags. if `s` is in error, that is a decoder bug, please report it.


## stability
0.1 and 1.0 versions are considered significant indicators of feature-completeness and stability. the specific guidelines by which `yaxpeax-arm` will be considered stable are listed below.

### 0.1 checklist
- [ ] support `NEON`
- [ ] adjust `yaxpeax-arch` so `min_length` can be contingent on the mode of `InstDecoder`
  - currently `min_length` is always 4, which is incorrect for `Thumb` modes.
    conversely, selecting "2" would be flagrantly wrong for `ARM` modes.
- [ ] address all in-tree TODO

### 1.0 checklist
- [ ] support per-version decode flags, so decoding an armv4, armv5, or armv7 instruction
- [ ] fully support `should_is_must` to control how pedantic decoding should be
- [ ] fully support reporting `unpredictable` encodings as `DecodeError::Unpredictable` if required
- [ ] exhaustively test armv7 and armv8 instructions against other decoders
  - existing thumb test suite is derived from enumerating thumb instructions,
    but is missing some

### ! user beware !
* armv7 NEON support is still nonexistent

## arch notes:

### Register Names
Reproduced from [infocenter.arm.com](http://infocenter.arm.com/help/index.jsp?topic=/com.arm.doc.dui0473c/CJAJBFHC.html):
| Name | Maps To | Meaning |
| ---- | ------- | ------- |
| r0-r15 | r0-r15 | These are the the registers! |
| a1-a4 | r0-r3 | Argument, result, or scratch registers |
| v1-v8 | r4-r11 | Variable registers |
| sb | r9 | Static base register |
| fp | r11 | Frame pointer\* |
| ip | r12 | Intra-procedure call register |
| sp | r13 | Stack pointer |
| lr | r14 | link register |
| pc | r15 | program counter |

\* `fp` does not appear to be explicitly referenced in ARM documentation, and mapping to r11 looks to be OS (Windows/Linux?) convention.
