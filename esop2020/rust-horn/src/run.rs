use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::{Compiler, Config};
use rustc_interface::Queries;
use rustc_session::config::OptLevel;

use std::env::args as get_args;
use std::path::PathBuf;

use crate::drive::{drive_rust_horn, Options};

struct MyCallbacks {
  opts: Options,
}
impl Callbacks for MyCallbacks {
  fn config(&mut self, config: &mut Config) {
    let opts = &mut config.opts;
    opts.optimize = OptLevel::Aggressive;
    opts.debug_assertions = false;
  }
  fn after_analysis<'tcx>(
    &mut self, _compiler: &Compiler, queries: &'tcx Queries<'tcx>,
  ) -> Compilation {
    queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
      let res = drive_rust_horn(tcx, &self.opts);
      res.unwrap();
    });
    Compilation::Stop
  }
}

pub fn run_rust_horn() {
  println!("RustHorn!");
  let mut opts = Options::default();
  let mut args = Vec::new();
  let mut args_iter = get_args();
  while let Some(arg) = args_iter.next() {
    if arg == "-o" {
      opts.output_file = PathBuf::from(args_iter.next().unwrap());
    } else if arg == "-d" {
      opts.prettify_dir = PathBuf::from(args_iter.next().unwrap());
    } else if arg == "--mir" {
      opts.mir = true;
    } else if arg == "--no-mir" {
      opts.mir = false;
    } else if arg == "--mir-dot" {
      opts.mir_dot = true;
    } else if arg == "--no-mir-dot" {
      opts.mir_dot = false;
    } else {
      args.push(arg);
    }
  }
  let res = run_compiler(&args, &mut MyCallbacks { opts }, None, None);
  res.unwrap();
}
