# The `rust-horn` Crate

This is the latest `rust-horn` crate.

It works for `rustc 1.45.0-nightly (75e1463c5 2020-05-13)`.
Since `rust-horn` leverages [Rust's MIR](https://rust-lang.github.io/rustc-guide/mir/index.html), it depends on Rust's nightly APIs, which are subject to rapid change.

Currently this crate is experimental and not very mature.
Pull requests for improvements and extensions are welcomed.

## Supported Features

- [x] Loops and recursions
- [x] Recursive types
- [ ] Arrays, vectors and slices
- [ ] Function pointers
- [ ] Closures
- [ ] Two-phase borrows
- [ ] `Cell`, `RefCell`, etc.
