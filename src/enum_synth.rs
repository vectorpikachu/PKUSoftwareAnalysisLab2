//! 实现最基础的枚举合成器

use std::borrow::Borrow;
use std::env;
use std::fs;
use std::sync::Arc;

use z3::Config;

use crate::base::language;
use crate::base::language::subst_once;
use crate::base::language::Exp;
use crate::base::language::Terms;
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

    // 获取所有满足 返回值类型 的非终结符对应的 Rule
    let mut start_rules = &Vec::new();

    for rule in synth_fun.get_all_rules() {
        if synth_fun.get_type(&rule.0) == Some(synth_fun.get_return_type()) {
            start_rules = synth_fun.get_rules(&rule.0).unwrap();
        }
    }
    
    // 创建一个 queue 用于枚举
    let mut queue = Vec::new();
    for rule in start_rules {
        queue.push(rule.get_body().clone());
    }

    let mut id = 0;
    let non_terminal_checker = synth_fun.get_non_terminal_checker();

    // println!("Start enumerating... {:#?}", queue.get(id).unwrap());
    // let term_map = queue.get_mut(id).unwrap().get_counts(non_terminal_checker);
    // println!("{:#?}", term_map);

    loop {
        // 取出 queue 里面的第一个元素
        let mut current_exp = queue.get(id).unwrap().clone();
        id += 1;
        println!("Current exp: {:#?}", &current_exp);
        let mut non_term = language::count_vars_occurrence(&mut current_exp, &non_terminal_checker);        
        println!("Non-terminals: {:#?}", &non_term);

        let mut input = String::new();
        std::io::stdin().read_line(&mut input).expect("Failed to read line");  

        if non_term.is_empty() {
            continue;
        }

        // 尝试扩展 current_exp
        for rules in synth_fun.get_all_rules() {
            if non_term.contains_key(rules.0) {
                for rule in rules.1.iter() {
                    // 从 non_term 中取出可变引用
                    // {
                    //     let rep_loc = &mut non_term.get_mut(rules.0).unwrap()[0];
                    //     let pre_exp = (**rep_loc).clone();
                    //     **rep_loc = rule.get_body().clone();
                    //     println!("Try replacing {:#?} with {:#?}", &pre_exp, &rule.get_body());
                    // }
                    // println!("{:#?}", &mut current_exp);
                }
            }
        }

    }

    // println!("Terminals: {:#?}", terminals);

    // for define in defines {
    //     let my_func = define.get_name();
    //     if my_func == "mul3mod10" {
    //         let counterexampleorsat = solver.get_counterexample(&define.to_basic_fun());
    //         match counterexampleorsat {
    //             Ok(c) => {
    //                 println!("Counterexample: {:#?}", c);
    //             }
    //             Err(e) => {
    //                 println!("No counterexample found: {}", e);
    //             }
    //         }
    //     }
    // }
    

}