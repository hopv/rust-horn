use rustc::ty::TyCtxt;

use std::fs::File;
use std::io::{Result, Write};
use std::path::PathBuf;

use crate::analyze::analyze;
use crate::prettify::{pr_mir, pr_mir_dot, pr_name};
use crate::represent::rep_summary;
use crate::util::enumerate_mirs;

pub struct Options {
  pub output_file: PathBuf,
  pub prettify_dir: PathBuf,
  pub mir: bool,
  pub mir_dot: bool,
}
impl Default for Options {
  fn default() -> Self {
    Options {
      prettify_dir: PathBuf::from("out"),
      output_file: PathBuf::from("out.smt2"),
      mir: false,
      mir_dot: false,
    }
  }
}

pub fn drive_rust_horn(tcx: TyCtxt, opts: &Options) -> Result<()> {
  for (fun, mir) in enumerate_mirs(tcx) {
    let fun_name = pr_name(fun);
    if opts.mir {
      let mut mir_file = File::create(opts.prettify_dir.join(format!("{}.mir", &fun_name)))?;
      write!(&mut mir_file, "{}", pr_mir(mir, fun, tcx))?;
    }
    if opts.mir_dot {
      let mut dot_file = File::create(opts.prettify_dir.join(format!("{}.dot", &fun_name)))?;
      write!(&mut dot_file, "{}", pr_mir_dot(mir, fun, tcx))?;
    }
  }
  let summary = analyze(tcx);
  let mut output_file = File::create(&opts.output_file)?;
  write!(&mut output_file, "{}", rep_summary(&summary, tcx))?;
  Ok(())
}
