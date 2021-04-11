# Materials for the TOPLAS 2021 Paper

- [rust-horn](./rust-horn): RustHorn implementation used for the experiments
- [benchmarks](./benchmarks): Benchmarks and experimental results

## Dependencies

- Rust Compiler: `rustc 1.53.0-nightly (07e0e2ec2 2021-03-24)`
- Spacer: [`z3 4.8.10`](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.10)
- HoIce: [`hoice 1.8.3`](https://github.com/hopv/hoice); [`z3 4.7.1`](https://github.com/Z3Prover/z3/releases/tag/z3-4.7.1) should be used as a backend SMT solver to deal well with recursive data types
- SeaHorn: `seahorn 0.1.0-rc3-e712712` in [Docker's `seahorn/seahorn-llvm5`](https://hub.docker.com/r/seahorn/seahorn-llvm5)
