# Materials for the TOPLAS 2021 Paper

- [rust-horn](./rust-horn): RustHorn implementation used for the experiments
- [benchmarks](./benchmarks): Benchmarks and experimental results

## Dependencies

- Rust Compiler: `rustc 1.53.0-nightly (b84932674 2021-04-21)`
- Spacer: [`z3 4.8.10`](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.10)
- HoIce: [`hoice 1.9.0`](https://github.com/hopv/hoice); [`z3 4.7.1`](https://github.com/Z3Prover/z3/releases/tag/z3-4.7.1) should be used as a backend SMT solver to deal well with recursive data types
- SeaHorn: `seahorn 10.0.0-rc0-86a31cf1` in [Docker's `seahorn/seahorn-llvm10:nightly`](https://hub.docker.com/r/seahorn/seahorn-llvm10)
