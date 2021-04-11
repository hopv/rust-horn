use rustc_driver::{Callbacks, Compilation, RunCompiler};
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
    match arg.as_str() {
      "-o" => opts.output_file = PathBuf::from(args_iter.next().unwrap()),
      "-d" => opts.prettify_dir = PathBuf::from(args_iter.next().unwrap()),
      "--mir" => opts.mir = true,
      "--no-mir" => opts.mir = false,
      "--mir-dot" => opts.mir_dot = true,
      "--no-mir-dot" => opts.mir_dot = false,
      _ => args.push(arg),
    };
  }
  RunCompiler::new(&args, &mut MyCallbacks { opts }).run().unwrap();
}
