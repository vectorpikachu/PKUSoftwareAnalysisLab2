//! 实现最基础的枚举合成器

use std::collections::HashSet;
use std::env;
use std::fs;
use std::sync::Arc;

use either::Either::Left;
use either::Either::Right;
use z3::Config;

use crate::base;
use crate::base::language::BasicFun;
use crate::base::language::Exp;
use crate::base::language::Rule;
use crate::base::language::SynthFun;
use crate::base::language::Terms;
use crate::base::logic::parse_logic_tag;
use crate::base::scope::Scope;
use crate::exp;
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
    fs::read_to_string(file_name)
        .map_err(|_| {
            eprintln!("File not found");
            std::process::exit(1);
        })
        .unwrap()
}

/// 设计一个枚举合成器
pub fn enum_synth_fun() {
    let cmds = read_file();
    println!("{}", cmds);
    let sexps = sexp::parse(&cmds);
    let sexps = match sexps {
        Ok(v) => v,
        Err(e) => panic!("Error: {:?}", e),
    };
    let sexps = match sexps {
        sexp::Sexp::List(v) => v,
        _ => panic!("Expected a list"),
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
            Ok(c) => match c {
                Command::DefineFun(d) => {
                    defines.push(d);
                }
                Command::DeclareVar(v) => {
                    declare_vars.push(v);
                }
                Command::SynthFun(s) => {
                    synth_func = Some(s);
                }
                Command::Constraint(c) => {
                    constraints.push(c);
                }
                Command::SetLogic(s) => {
                    println!("Set logic to {}", s.to_string());
                }
                _ => {}
            },
            Err(e) => {
                panic!("Error: {:?}", e);
            }
        }
    }

    let synth_fun = match synth_func {
        Some(s) => s,
        None => panic!("No synth function defined"),
    };

    // let rc_context = Arc::new(ctx);

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
        &synth_fun.clone(),
        constraints,
        &z3_ctx,
    );

    println!("Synthesizing function: {:#?}", solver.get_synth_fun());

    let mut prog_size = 1;

    let mut candidate_exprs = Vec::new();
    // 先把初始的的所有 类型满足的终结符加入
    candidate_exprs.extend(synth_fun.get_all_exp());
    println!("Now Candidate exprs: {:#?}", candidate_exprs);

    let expr_set: HashSet<Exp<String, lia::Values>> = HashSet::new();

    let exp = Exp::Apply(
        "mod".to_string(),
        vec![
            Exp::Apply(
                "*".to_string(),
                vec![
                    Exp::Value(Terms::Var("Start".to_string())),
                    Exp::Value(Terms::PrimValue(lia::Values::Int(3))),
                ],
            ),
            Exp::Value(Terms::PrimValue(lia::Values::Int(10))),
        ],
    );
    let ext = extend_expr(&synth_fun, &exp, &expr_set, &mut candidate_exprs);
    println!("Extend: {:#?}", ext);

    let exp = Exp::Apply(
        "mod".to_string(),
        vec![
            Exp::Apply(
                "*".to_string(),
                vec![
                    Exp::Value(Terms::Var("x".to_string())),
                    Exp::Value(Terms::PrimValue(lia::Values::Int(3))),
                ],
            ),
            Exp::Value(Terms::PrimValue(lia::Values::Int(10))),
        ],
    );
    let prog = synth_fun.exp_to_basic_fun(Some(&ctx), &exp);
    let ce = solver.get_counterexample(&prog);
    println!("Counterexample: {:#?}", ce);

    let mut counter_examples = Vec::new();

    loop {
        let now_exprs = enumerate_exprs(&synth_fun, &mut candidate_exprs, prog_size, &expr_set);
        println!("Now Candidate exprs: {:#?}", candidate_exprs);
        for expr in now_exprs {
            if check_terminal(&expr, &synth_fun) {
                let now_prog = synth_fun.exp_to_basic_fun(Some(&ctx), &expr);

                println!("Now Program: {:#?}", expr);
                // 首先计算是否满足先前返回的反例
                // TODO: 反例到底是个什么东西?
                if !counter_examples.is_empty() {
                    for counter_example in counter_examples.iter() {
                        // 直接传给z3判断
                    }
                }

                // 由于 ctx 一直保存着之前的, 所以必须重新创建一个新的
                let z3_ctx = z3::Context::new(&Config::default());
                let mut solver = z3_solver::Z3Solver::new(
                    defines,
                    declare_vars,
                    &synth_fun.clone(),
                    constraints,
                    &z3_ctx,
                );

                let res = solver.get_counterexample(&now_prog);
                match res {
                    Ok(either_val) => match either_val {
                        Left(v) => {
                            println!("Found counterexample: {:#?}", v);
                            counter_examples.push(v);
                        }
                        Right(e) => {
                            println!("Successfully Synthesis: {:#?}", e);
                            return;
                        }
                    },
                    Err(e) => {
                        panic!("Error: {:?}", e);
                    }
                }
            }
        }

        prog_size += 1;
        if prog_size > 4 {
            break;
        }
    }
}

fn check_terminal(
    exp: &Exp<String, lia::Values>,
    synth_fun: &SynthFun<String, lia::Values, lia::Types>,
) -> bool {
    match exp {
        Exp::Value(v) => match v {
            Terms::PrimValue(_pv) => true,
            Terms::Var(v) => synth_fun.is_terminal(v),
        },
        _ => false,
    }
}

/// 得到当前 prog_size 的所有表达式
/// prog_size 表示一个程序里的所有字符的长度
fn enumerate_exprs(
    synth_fun: &SynthFun<String, lia::Values, lia::Types>,
    candidate_exprs: &mut Vec<Exp<String, lia::Values>>,
    prog_size: i32,
    expr_set: &HashSet<Exp<String, lia::Values>>,
) -> Vec<Exp<String, lia::Values>> {
    let mut new_exprs = Vec::new();
    for expr in candidate_exprs.clone() {
        let (terminals, non_terminals) = get_all_counts(synth_fun, &expr);
        if terminals == prog_size && non_terminals == 0 {
            new_exprs.push(expr.clone());
        } else if terminals + non_terminals <= prog_size && non_terminals > 0 {
            // TODO: 如何枚举生成新的表达式?
            let now_exprs = extend_expr(synth_fun, &expr, expr_set, candidate_exprs);
            for new_expr in now_exprs {
                if !expr_set.contains(&new_expr) {
                    new_exprs.push(new_expr);
                }
            }
        } else if terminals < prog_size && non_terminals == 0 {
            // 无论如何也产生不了新的表达式
            continue;
        }
    }

    return new_exprs;
}

/// 返回 (terminals, non_terminals)
fn get_all_counts(
    synth_fun: &SynthFun<String, lia::Values, lia::Types>,
    expr: &Exp<String, lia::Values>,
) -> (i32, i32) {
    match expr {
        Exp::Value(v) => match v {
            Terms::PrimValue(_pv) => (1, 0),
            Terms::Var(v) => {
                if synth_fun.is_terminal(v) {
                    (1, 0)
                } else {
                    (0, 1)
                }
            }
        },
        Exp::Apply(_f, args) => {
            let mut terminals = 1; // 函数名算为一个终结符
            let mut non_terminals = 0;
            for arg in args {
                let (t, n) = get_all_counts(synth_fun, arg);
                terminals += t;
                non_terminals += n;
            }
            (terminals, non_terminals)
        }
    }
}

fn extend_expr(
    synth_fun: &SynthFun<String, lia::Values, lia::Types>,
    expr: &Exp<String, lia::Values>,
    expr_set: &HashSet<Exp<String, lia::Values>>,
    candidate_exprs: &mut Vec<Exp<String, lia::Values>>,
) -> Vec<Exp<String, lia::Values>> {
    let mut new_exprs = Vec::new();
    match expr {
        Exp::Value(v) => match v {
            Terms::PrimValue(_pv) => {
                // 无法扩展
            }
            Terms::Var(v) => {
                if synth_fun.is_terminal(v) {
                    // 无法扩展
                } else {
                    // 扩展
                    let rules = synth_fun.get_rules(v);
                    match rules {
                        Some(rules) => {
                            for rule in rules {
                                let new_expr =
                                    rule.subst_non_terminal_once(expr.clone(), v, rule.get_body());
                                println!("New expr: {:#?}", new_expr);
                                new_exprs.push(new_expr);
                            }
                        }
                        None => {
                            // 无法扩展
                        }
                    }
                }
            }
        },
        Exp::Apply(_f, args) => {
            // 扩展 args
            for arg in args {
                let new_exprs_arg = extend_expr(synth_fun, arg, expr_set, candidate_exprs);
                for new_expr_arg in new_exprs_arg {
                    let new_expr = exp::apply_exp(_f.clone(), vec![new_expr_arg.clone()]);
                    new_exprs.push(new_expr);
                }
            }
        }
    }
    return new_exprs;
}
