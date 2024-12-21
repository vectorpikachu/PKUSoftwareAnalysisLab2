pub mod base;
pub mod exp;
pub mod lia_logic;
pub mod parser;
pub mod z3_solver;
pub mod enum_synth;
fn main() {
    enum_synth::enum_synth_fun();
    println!("Hello, world!");
}