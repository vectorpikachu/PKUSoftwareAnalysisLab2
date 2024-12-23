use either::Either::Left;

pub mod base;
pub mod exp;
pub mod lia_logic;
pub mod parser;
pub mod z3_solver;
pub mod enum_synth;
fn main() {
    let res = enum_synth::enum_synth_fun();
    
    // 写进 result.txt
    use std::fs::File;
    use std::io::Write;
    let mut file = File::create("result.txt").unwrap();
    match res {
        Left(s) => {
            file.write_all(s.as_bytes()).unwrap();
        },
        _ => {
            panic!("Error");
        }
    }

    println!("Hello, world!");
}
