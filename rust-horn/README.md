# The `rust-horn` Crate

The latest version of the `rust-horn` crate.

This version works for `rustc 1.53.0-nightly (07e0e2ec2 2021-03-24)`.
Since `rust-horn` uses [Rust's MIR](https://rust-lang.github.io/rustc-guide/mir/index.html), it depends on very unstable APIs of `rustc_*` creates.
Please check the version of `rustc` before you try the verifier.

You can build the verifier by `make build`.
You can try the verifier for `./sample.v` by `make try`.
(Please modify the variable `RUST_LIB_PATH` in `Makefile` depending on your platform.)

## Supported Features

- [x] Loops and recursions
- [x] Recursive types
- [ ] Arrays, vectors and slices
- [ ] Function pointers
- [ ] Closures
- [ ] Two-phase borrows
- [ ] `Cell`, `RefCell`, etc.
