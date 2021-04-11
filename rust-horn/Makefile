.PHONY: build try try-mir try-clean

build:
	cargo fmt
	cargo build --release

RUST_LIB_PATH = $(HOME)/.multirust/toolchains/nightly-x86_64-apple-darwin/lib/rustlib/x86_64-apple-darwin/lib/

try:
	for file in sample/*.rs; do \
		name=$${file%.rs}; \
		cargo run --release \
			"$$name.rs" -o "$$name.smt2" \
			-L $(RUST_LIB_PATH); \
	done

try-clean:
	rm -f sample/*.smt2
	rm -f sample/*.mir
