# Materials for the TOPLAS 2021 Paper

- [rust-horn](./rust-horn): RustHorn implementation used for the experiments
- [benchmarks](./benchmarks): Benchmarks and experimental results

## Dependencies

- Rust Compiler: `rustc 1.45.0-nightly (a74d1862d 2020-05-14)`
- Spacer: [`z3 4.8.8`](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.8)
- HoIce: [`hoice 1.8.1`](https://github.com/hopv/hoice); [`z3 4.7.1`](https://github.com/Z3Prover/z3/releases/tag/z3-4.7.1) is used as a backend SMT solver to deal well with recursive data types
- SeaHorn: `seahorn 0.1.0-rc3-e712712` in [Docker's `seahorn/seahorn-llvm5`](https://hub.docker.com/r/seahorn/seahorn-llvm5)
