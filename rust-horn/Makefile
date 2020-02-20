.PHONY: out clean

RUST_LIB_PATH = $(HOME)/.multirust/toolchains/nightly-x86_64-apple-darwin/lib/rustlib/x86_64-apple-darwin/lib/

RUST_HORN_LIB_PATH = ../rust-horn-lib/target/release/
RUST_HORN_PLUGIN_PATH = ../rust-horn-plugin/target/release/

TRY_PATH = ../try/src/main.rs
OUT_FILE = ../try/out.smt2
OUT_DIR = ../try/out

OPTIONS = $(TRY_PATH) -L $(RUST_LIB_PATH) \
	-L $(RUST_HORN_LIB_PATH) -L $(RUST_HORN_PLUGIN_PATH) \
	-o $(OUT_FILE) -d $(OUT_DIR)

.PHONY: debug release out dots clean

debug:
	cargo fmt
	env RUST_BACKTRACE=1 cargo run $(OPTIONS) --mir-dot

out:
	cargo run --release $(OPTIONS)

z3:
	z3 $(OUT_FILE)

dots:
	./dots $(OUT_DIR)

clean:
	rm $(OUT_FILE)
	rm -f $(OUT_DIR)/*
