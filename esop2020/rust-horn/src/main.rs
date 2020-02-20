#![feature(rustc_private)]
#![feature(box_syntax, box_patterns)]
#![feature(pattern)]

extern crate rustc;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_mir;
extern crate rustc_session;
extern crate rustc_span;
extern crate syntax;

#[macro_use]
mod util;

mod analyze;
mod drive;
mod prettify;
mod represent;
mod run;

fn main() { run::run_rust_horn(); }
