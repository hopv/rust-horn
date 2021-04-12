SHELL = /bin/bash

.PHONY: horn

RUST_LIB_PATH = $(HOME)/.multirust/toolchains/nightly-x86_64-apple-darwin/lib/rustlib/x86_64-apple-darwin/lib/

RUST_HORN_PATH = ../../rust-horn/Cargo.toml

TARGET = *

horn:
	for file in $(TARGET)/*.rs; do \
		name=$${file%.rs}; \
		time cargo run --release --manifest-path=$(RUST_HORN_PATH) \
			"$$name.rs" -o "$$name.smt2" \
			-L $(RUST_LIB_PATH); \
	done

bench-z3:
	OUT=bench-z3; \
	> $$OUT; \
	for file in $(TARGET)/*.smt2; do \
		echo "$$ z3 $$file" | tee -a $$OUT; \
		(time z3 "$$file" -T:180) 2>&1 | tee -a $$OUT; \
		echo "" | tee -a $$OUT; \
	done

bench-hoice:
	OUT=bench-hoice; \
	> $$OUT; \
	for file in $(TARGET)/*.smt2; do \
		echo "$$ hoice $$file" | tee -a $$OUT; \
		(time hoice "$$file" -t 180) 2>&1 | tee -a $$OUT; \
		echo "" | tee -a $$OUT; \
	done
