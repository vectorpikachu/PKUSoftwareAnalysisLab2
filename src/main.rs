pub mod base;
pub mod exp;
pub mod lia_logic;
pub mod parser;
pub mod z3_solver;

use std::fs::File;
use std::io::{self, Read};
use std::path::Path;

use sexp::Error;

fn read_sl_file<P: AsRef<Path>>(path: P) -> io::Result<String> {
    // let mut file = File::open(path)? -> io:Result<()> ;
    let mut file = File::open(path)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    Ok(contents)
}

// fn parse_sl_file<P: AsRef<Path>>(path: P) -> Vec<sexp::Sexp {

    // let mut 
// }
fn main() -> io::Result<()> {
    let path = "judge/global/tests/open_basic/tutorial.sl";
    let content = read_sl_file(path)?;
    println!("{:?}", content);

    Ok(())
    // let sexps = parse_
}
