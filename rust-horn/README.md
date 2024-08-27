# The `rust-horn` Crate

The latest version of the `rust-horn` crate.

This version works for `rustc 1.60.0-nightly (17d29dcdc 2022-01-21)`.
Since `rust-horn` uses [Rust's MIR](https://rust-lang.github.io/rustc-guide/mir/index.html), it depends on very unstable APIs of `rustc_*` creates.
Please check the version of `rustc` before you try the verifier.

You can build the verifier by `make build`.
You can try the verifier for the files `sample/*.rs` by `make try`.

## Supported Features

- [x] Recursions
- [ ] Loops
- [x] Recursive types
- [ ] Arrays, vectors and slices
- [ ] Function pointers
- [ ] Closures
- [ ] Two-phase borrows
- [ ] `Cell`, `RefCell`, etc.
