//! 实现最基础的枚举合成器

use std::env;
use std::fs;
use std::sync::Arc;

use z3::Config;

use crate::lia_logic::lia;
use crate::parser::parser::MutContextSexpParser;
use crate::parser::rc_function_var_context::Command;
use crate::z3_solver;

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
    fs::read_to_string(file_name).map_err(|_| {
        eprintln!("File not found");
        std::process::exit(1);
    }).unwrap()
}

/// 设计一个枚举合成器
pub fn enum_synth_fun() {
    let cmds = read_file();
    println!("{}", cmds);
    let sexps = sexp::parse(&cmds);
    let sexps = match sexps {
        Ok(v) => v,
        Err(e) => panic!("Error: {:?}", e)
    };
    let sexps = match sexps {
        sexp::Sexp::List(v) => v,
        _ => panic!("Expected a list")
    };
    println!("{:#?}", sexps);
    let mut ctx = lia::get_empty_context_with_builtin();
    let mut defines = Vec::new();
    let mut declare_vars = Vec::new();
    let mut synth_func = None;
    let mut constraints: Vec<crate::base::language::Constraint<String, lia::Values>> = Vec::new();
    for exp in sexps {
        let parse_exp = Command::<String, lia::Values, lia::Types>::parse(&exp, &mut ctx);
        match parse_exp {
            Ok(c) => {
                match c {
                    Command::DefineFun(d) => {
                        defines.push(d);
                    },
                    Command::DeclareVar(v) => {
                        declare_vars.push(v);
                    },
                    Command::SynthFun(s) => {
                        synth_func = Some(s);
                    },
                    Command::Constraint(c) => {
                        constraints.push(c);
                    }
                    Command::SetLogic(s) => {
                        println!("Set logic to {}", s.to_string());
                    }
                    _ => {}
                }
            }
            Err(e) => {
                panic!("Error: {:?}", e);
            }
        }
    }

    let mut synth_fun = match synth_func {
        Some(s) => {
            s
        }
        None => panic!("No synth function defined"),
    };
    

    let rc_context = Arc::new(ctx);
    for define in defines.clone() {
        match define.context.set(rc_context.clone()) {
            Ok(_) => (),
            Err(_) => panic!("Error")   // 不应出现
        }
    }

    /*
     * 如何把 builtin 函数加入? 
     */

    let defines = defines.as_slice();
    let declare_vars = declare_vars.as_slice();
    let constraints = constraints.as_slice();
    let z3_ctx = z3::Context::new(&Config::default());
    let mut solver = z3_solver::Z3Solver::new(
        defines,
        declare_vars,
        &synth_fun,
        constraints,
        &z3_ctx
    );

    // 首先获取所有符合返回值的 终结符
    let mut terminals = Vec::new();
    synth_fun.init_counts();
    // 得到 Start 里面的所有终结符
    let start_rules = synth_fun.get_rules(&"Start".to_string()).unwrap();
    for rule in start_rules {
        if rule.is_terminal() {
            terminals.push(rule);
        }
    }

    println!("Terminals: {:#?}", terminals);

    println!("Synthesizing function: {:#?}", solver.get_synth_fun());

    
    let my_synth_fun = "((define-fun max2 ((x Int) (y Int)) Int (ite (>= x y) x y)))";
    let my_exp = sexp::parse(my_synth_fun).unwrap();
    let mut parse_exp =Command::<String, lia::Values, lia::Types>::parse(&my_exp, &mut ctx);
    

}