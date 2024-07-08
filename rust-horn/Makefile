SHELL = /bin/bash

.PHONY: build try try-mir clean

build:
	cargo fmt
	cargo build --release

RUST_LIB_PATH = $(shell rustc --print target-libdir)

try:
	for file in sample/*.rs; do \
		name=$${file%.rs}; \
		cargo run --release \
			"$$name.rs" -o "$$name.smt2" \
			-- -L $(RUST_LIB_PATH); \
	done

clean:
	cargo clean
	rm -f sample/*.smt2
	rm -f sample/*.mir
