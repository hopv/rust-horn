# Materials for the ESOP 2020 Paper

Materials for the paper [RustHorn: CHC-based Verification for Rust Programs (ESOP 2020)](https://link.springer.com/chapter/10.1007%2F978-3-030-44914-8_18).

- [rust-horn](./rust-horn): RustHorn implementation used for the experiments
- [benchmarks](./benchmarks): Benchmarks and experimental results

## Dependencies

- Rust Compiler: `rustc 1.43.0-nightly (e620d0f33 2020-02-18)`
- Spacer: [`z3 4.8.7`](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.7)
- HoIce: [`hoice 1.8.1`](https://github.com/hopv/hoice); [`z3 4.7.1`](https://github.com/Z3Prover/z3/releases/tag/z3-4.7.1) is used as a backend SMT solver to deal well with recursive data types
- SeaHorn: `seahorn 0.1.0-rc3` in [Docker's `seahorn/seahorn`](https://hub.docker.com/r/seahorn/seahorn/)
