//! 实现最基础的枚举合成器

use std::collections::HashMap;
use std::collections::HashSet;
use std::env;
use std::fs;
use std::rc;
use std::sync::Arc;

use either::Either;
use either::Either::Left;
use either::Either::Right;
use z3::Config;

use crate::base;
use crate::base::function::GetValueError;
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
    let mut candidate_exprs: HashMap<i32, HashMap<String, Vec<Exp<String, lia::Values>>>> = HashMap::new();
    candidate_exprs.insert(prog_size, HashMap::new());
    for rule in synth_fun.get_all_rules() {
        candidate_exprs.get_mut(&prog_size).unwrap().insert(rule.0.clone(), vec![]);
        for production in rule.1 {
            let now_expr = production.get_body().clone();
            if !check_terminal(&now_expr, &synth_fun) {
                continue;
            }
            candidate_exprs
                .get_mut(&prog_size)
                .unwrap()
                .get_mut(rule.0)
                .unwrap()
                .push(now_expr);
        }
    }
    println!("Candidate exprs: {:#?}", candidate_exprs);
    
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

    let mut counter_examples: Vec<HashMap<String, (lia::Types, lia::Values)>> = Vec::new();

    /* 
    loop {
        let now_exprs = enumerate_exprs(&synth_fun, &mut candidate_exprs, prog_size);
        println!("Now Candidate exprs: {:#?}", candidate_exprs);
        for expr in now_exprs {
            if check_terminal(&expr, &synth_fun) {
                let now_prog = synth_fun.exp_to_basic_fun(Some(&ctx), &expr);

                println!("Now Program: {:#?}", expr);
                // 首先计算是否满足先前返回的反例
                // 反例是一个 HashMap<String, (Type, Value)>

                if !counter_examples.is_empty() {
                    for counter_example in counter_examples.iter() {
                        // 直接传给z3判断
                        for constraint in constraints {
                            let passed = constraint.instantiate_and_execute(
                                &synth_fun, 
                                Some(&ctx), 
                                &expr, 
                                |id| match counter_example.get(id) {
                                    Some((_, v)) => Ok(Either::Left(*v)),
                                    None => Err(GetValueError::VarNotDefinedWhenGet("Var not defined when get in test conunter examples".to_string()))
                                }
                            );
                        }
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
    }*/
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

/// 枚举 prog_size 的所有表达式
/// 比如说 Expr -> Expr + Expr, 那么就去
/// candidate_exprs[x1][Expr] 和 candidate_exprs[x2][Expr] 枚举
/// x1 + x2 = prog_size
/// 如果有 k 个非终结符, 则 x1 + x2 + ... + xk = prog_size
/// 所有的结果会被写入 candidate_exprs[prog_size] 中
fn enumerate_exprs(
    synth_fun: &SynthFun<String, lia::Values, lia::Types>,
    candidate_exprs: &mut HashMap<i32, HashMap<String, Vec<Exp<String, lia::Values>>>>,
    prog_size: i32,
) {
    
}