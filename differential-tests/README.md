on aarch64 you really want `RUSTFLAGS="-C target-feature=+lse"` (if your aarch64 target supports armv8.1).

without +lse you'll get outlined atomics for the per-thread atomic add/stat tracking, which means each atomic add is a call/feature test/return instead of ... just the op.
