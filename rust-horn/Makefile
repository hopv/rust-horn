SHELL = /bin/bash

.PHONY: build try clean

build:
	cargo fmt
	cargo build --release

RUST_LIB_PATH = $(shell rustc --print target-libdir)

BENCH_DIR := ./sample
BENCHES := $(wildcard $(BENCH_DIR)/*.rs)

try: build $(BENCHES:$(BENCH_DIR)/%.rs=$(BENCH_DIR)/%.smt2)
	echo "done"

$(BENCH_DIR)/%.smt2: $(BENCH_DIR)/%.rs
	cargo run --release \
		"$<" -o "$@" \
		-- -L $(RUST_LIB_PATH)

clean:
	cargo clean
	rm -f sample/*.smt2
	rm -f sample/*.mir
