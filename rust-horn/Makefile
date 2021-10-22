SHELL = /bin/bash

.PHONY: build try try-mir clean

build:
	cargo fmt
	cargo build --release

# Please specify the appropriate path to the standard library in your platform
# TODO: Make this portable
RUST_LIB_PATH = ~/.rustup/toolchains/nightly-2021-04-21-aarch64-apple-darwin/lib/rustlib/aarch64-apple-darwin/lib

try:
	for file in sample/*.rs; do \
		name=$${file%.rs}; \
		cargo run --release \
			"$$name.rs" -o "$$name.smt2" \
			-L $(RUST_LIB_PATH); \
	done

clean:
	cargo clean
	rm -f sample/*.smt2
	rm -f sample/*.mir
