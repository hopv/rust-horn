.PHONY: build test

build:
	cargo fmt
	cargo build --release

RUST_LIB_PATH = $(HOME)/.multirust/toolchains/nightly-x86_64-apple-darwin/lib/rustlib/x86_64-apple-darwin/lib/

try:
	cargo run --release "./sample.rs" -o "./sample.smt2" -L $(RUST_LIB_PATH)
