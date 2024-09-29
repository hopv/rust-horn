#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(pattern)]

extern crate rustc_apfloat;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_type_ir;

mod util;

mod analyze;
mod library;
mod prettify;
mod represent;
mod types;

use rustc_driver::{Callbacks, Compilation, RunCompiler};
use rustc_interface::interface::{Compiler, Config};
use rustc_interface::Queries;
use rustc_session::config::OptLevel;

use std::env::args as get_args;
use std::fs::File;
use std::io::{Result, Write};
use std::path::PathBuf;

use crate::analyze::analyze;
use crate::prettify::{pr_mir, pr_mir_dot, pr_name};
use crate::represent::rep_summary;
use crate::types::{DefPathData, TyCtxt};

struct MyCallbacks {
    opts: Options,
}
impl Callbacks for MyCallbacks {
    fn config(&mut self, config: &mut Config) {
        let opts = &mut config.opts;
        opts.optimize = OptLevel::Aggressive;
        opts.debug_assertions = false;
        opts.cg.panic = Some(rustc_target::spec::PanicStrategy::Abort);
        // currently we do not want overflow checks, but
        // the mir builder may ignore this option
        // when the integer arithmetic function
        // get attributed `#[rustc_inherit_overflow_checks]`.
        opts.cg.overflow_checks = Some(false);
    }
    fn after_expansion<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().enter(|tcx| {
            let res = drive_rust_horn(tcx, &self.opts);
            res.unwrap();
        });
        Compilation::Stop
    }
}

fn main() {
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
            "--" => break,
            _ => args.push(arg),
        };
    }
    args.extend(args_iter);
    RunCompiler::new(&args, &mut MyCallbacks { opts }).run().unwrap();
}

struct Options {
    output_file: PathBuf,
    prettify_dir: PathBuf,
    mir: bool,
    mir_dot: bool,
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

fn drive_rust_horn(tcx: TyCtxt, opts: &Options) -> Result<()> {
    for fun in tcx.mir_keys(()).iter().map(|fun| fun.to_def_id()).filter(move |&fun| {
        tcx.def_path(fun).data.iter().all(|elem| !matches!(&elem.data, DefPathData::Ctor))
    }) {
        let mir = tcx.mir_built(fun.expect_local()).borrow();
        let fun_name = pr_name(fun);
        let prettify_dir = &opts.prettify_dir;
        if opts.mir {
            std::fs::create_dir_all(prettify_dir)?;
            let path = prettify_dir.join(&fun_name).with_extension("mir");
            let mut mir_file = File::create(path)?;
            write!(mir_file, "{}", pr_mir(&mir, fun, tcx))?;
        }
        if opts.mir_dot {
            std::fs::create_dir_all(prettify_dir)?;
            let path = prettify_dir.join(&fun_name).with_extension("dot");
            let mut dot_file = File::create(path)?;
            write!(dot_file, "{}", pr_mir_dot(&mir, fun, tcx))?;
        }
    }
    let summary = analyze(tcx);
    let path = &opts.output_file;
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let mut output_file = File::create(path)?;
    write!(output_file, "{}", rep_summary(&summary, tcx))?;
    Ok(())
}
