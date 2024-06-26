#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(pattern)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;

#[macro_use]
mod util;

mod analyze;
mod drive;
mod prettify;
mod represent;
mod run;

fn main() { run::run_rust_horn(); }
