use std::{env, fs};

use either::Either::Left;

pub mod base;
pub mod exp;
pub mod lia_logic;
pub mod bv_logic;
pub mod parser;
pub mod multi_threading;
pub mod z3_solver;
pub mod collect_callings;
pub mod lia_builtin;
pub mod bv_builtin;
pub mod enum_synth;
pub mod z3_builtin_checker;

/// 从命令行读取.sl文件
pub fn read_file() -> String {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: cargo run -- <file_name>");
        std::process::exit(1);
    }
    let file_name = &args[1];
    let file_type = file_name.split(".").last().unwrap();
    if file_type != "sl" {
        eprintln!("File type error: only .sl file is supported");
        std::process::exit(1);
    }
    fs::read_to_string(file_name)
        .map_err(|_| {
            eprintln!("File not found");
            std::process::exit(1);
        })
        .unwrap()
}

fn main() {
    let file = read_file();
    let res = enum_synth::enum_synth_fun(&file);
    
    // // 写进 result.txt
    use std::fs::File;
    use std::io::Write;
    let mut file = File::create("result.txt").unwrap();
    match res {
         Left(s) => {
             file.write_all(s.as_bytes()).unwrap();
             println!("{}", s);
         },
         _ => {
             panic!("Error");
         }
    }
}
