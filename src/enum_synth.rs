//! 实现最基础的枚举合成器

use std::collections::HashMap;
use std::env;
use std::fs;

use either::Either;
use either::Either::Left;
use either::Either::Right;
use z3::Config;

use crate::base::function::GetValueError;
use crate::base::language::ConstraintPassesValue;
use crate::base::language::Exp;
use crate::base::language::Rule;
use crate::base::language::SynthFun;
use crate::base::language::Terms;
use crate::lia_logic::lia;
use crate::lia_logic::lia::Values;
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
    let mut candidate_exprs: HashMap<i32, HashMap<String, Vec<Exp<String, lia::Values>>>> =
        HashMap::new();
    candidate_exprs.insert(prog_size, HashMap::new());
    for rule in synth_fun.get_all_rules() {
        candidate_exprs
            .get_mut(&prog_size)
            .unwrap()
            .insert(rule.0.clone(), vec![]);
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

    loop {
        let now_exprs = get_availabe_progs(
            &synth_fun,
            &candidate_exprs,
            prog_size,
            synth_fun.get_return_type(),
        );
        println!("Now Candidate exprs: {:#?}", candidate_exprs);
        for expr in now_exprs {
            if check_terminal(&expr, &synth_fun) {
                let now_prog = synth_fun.exp_to_basic_fun(Some(&ctx), &expr);

                println!("Now Program: {:#?}", expr);
                // 首先计算是否满足先前返回的反例
                // 反例是一个 HashMap<String, (Type, Value)>

                let mut pass_test = true;
                if !counter_examples.is_empty() {
                    for counter_example in counter_examples.iter() {
                        // 直接传给z3判断
                        for constraint in constraints {
                            let passed = constraint.get_body().instantiate_and_execute(
                                &synth_fun,
                                Some(&ctx),
                                &expr,
                                |id| match counter_example.get(id) {
                                    Some((_, v)) => Ok(Either::Left(*v)),
                                    None => Err(GetValueError::VarNotDefinedWhenGet(
                                        "Var not defined when get in test conunter examples"
                                            .to_string(),
                                    )),
                                },
                            );
                            if !passed.is_pass() {
                                pass_test = false;
                            }
                        }
                    }
                }

                if !pass_test {
                    continue;
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
        break;
        enumerate_exprs(&synth_fun, &mut candidate_exprs, prog_size);
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
    for id_rules in synth_fun.get_all_rules() {
        let id = id_rules.0;
        let rules = id_rules.1;
        for rule in rules {
            let mut actual_rule = rule.clone();
            let non_terminals = actual_rule.get_counts(
                synth_fun.get_non_terminal_checker()
            );
            let non_terminal_vecs = non_terminals.iter().map(|x| x.0.clone()).collect::<Vec<_>>();
            let mut result = HashMap::new(); 

            let mut actual_rule = rule.clone();
            dfs_all_non_terminals(
                &mut actual_rule, 
                &non_terminal_vecs, 
                &non_terminals, 
                candidate_exprs, 
                "Start".to_string(), 
                0, 
                prog_size, 
                prog_size, 
                id.clone(), 
                &mut result);

        }
    }
}

/// 得到候选程序中可用的表达式
fn get_availabe_progs(
    synth_fun: &SynthFun<String, lia::Values, lia::Types>,
    candidate_exprs: &HashMap<i32, HashMap<String, Vec<Exp<String, lia::Values>>>>,
    prog_size: i32,
    ty: &lia::Types,
) -> Vec<Exp<String, lia::Values>> {
    let mut availabe_progs = Vec::new();
    let possible_progs = candidate_exprs.get(&prog_size);
    if possible_progs.is_none() {
        return availabe_progs;
    };
    for (id, v) in possible_progs.unwrap().iter() {
        if *synth_fun.get_type(id).unwrap() != *ty {
            continue;
        }
        for exp in v {
            availabe_progs.push(exp.clone());
        }
    }

    availabe_progs
}


/// 现在比如 有一个 非终结符 `Start`. 
/// 有一个产生式 `Start -> Start + Start` 
/// 那么 `non_terminals["Start"] = vec![1, 2]`
/// 1,2 分别表示 第一个 `Start` 处的引用和第二个处的引用
/// 那么我们就应该
/// `(x1, x2)` 中的所有可能拼在一起把引用给 `actual_rule`
/// 然后得到 `actual_rule.get_body()` 就得到了一个全是终结符的合法程序
/// 此处应该写一个 DFS 来枚举所有的可能组合
fn dfs_all_non_terminals<'a>(
    actual_rule: &'a mut Rule<String, lia::Values>,
    non_terminal_vecs: &'a Vec<String>,
    non_terminals: &'a HashMap<String, Vec<&'a mut Exp<String, lia::Values>>>,
    candidate_exprs: &'a HashMap<i32, HashMap<String, Vec<Exp<String, lia::Values>>>>,
    cur_non_terminal: String,
    cur_prog: i32,
    left_prog_size: i32,
    total_prog_size: i32,
    id: String,
    result: &mut HashMap<String, Vec<Exp<String, lia::Values>>>,
) {
    // 剩余的为 0, 必须退出了
    if left_prog_size == 0 {
        if let Some(exps) = non_terminals.get(&cur_non_terminal) {
            if (cur_prog as usize) == exps.len() {
                // 如果 candidate_exprs[total_prog_size][id]没有的话就新建
                // 否则直接插入
                if candidate_exprs.get(&total_prog_size).is_none() {
                    result.insert(id, vec![actual_rule.get_body().clone()]);
                } else {
                    result.get_mut(&cur_non_terminal).unwrap().push(actual_rule.get_body().clone());
                }
            }
        }
        return;
    }

    for sz in 1..=left_prog_size {
        // 剩余的 program 大小为 sz, 那么应该从 candidate_exprs[sz] 中取值
        // 获取当前的 candidate_exprs[sz][cur_non_terminal]
        // 然后选择一个, 接着对 (cur_non_terminal, cur_prog)的下一个, left_prog_size - sz递归
        if let Some(cur_candidates) = candidate_exprs.get_mut(&sz) {
            if let Some(non_terminal_candidates) = cur_candidates.get_mut(&cur_non_terminal) {
                for candidate in non_terminal_candidates {
                    if let Some(exps) = non_terminals.get(&cur_non_terminal) {
                        if (cur_prog as usize) < exps.len() {
                            // 修改当前的非终结符引用为候选表达式
                            exps[cur_prog as usize] = candidate;
                            
                            // TODO: 可能我无法解决这里的关于可变引用的部分

                            let next_dfs = get_next(&cur_non_terminal, cur_prog, non_terminals, non_terminal_vecs);

                            // 递归调用，处理下一个非终结符
                            dfs_all_non_terminals(
                                actual_rule,
                                non_terminal_vecs,
                                non_terminals,
                                candidate_exprs,
                                next_dfs.0,
                                next_dfs.1,
                                left_prog_size - sz,
                                total_prog_size,
                                id.clone(),
                                result,
                            );
                        }
                    }
                }
            }
        }
    }
}

fn get_next(
    cur_non_terminal: &String, 
    cur_prog: i32, 
    non_terminals: &HashMap<String, Vec<&mut Exp<String, lia::Values>>>,
    non_terminal_vecs: &Vec<String>,
) -> (String, i32) {
    let now = non_terminals.get(cur_non_terminal).unwrap();
    
    let next_non_terminal: String;
    let next_prog: i32;

    if cur_prog + 1 >= now.len() as i32 {
        // 获取下一个非终结符
        let next_index = non_terminal_vecs.iter().position(|x| x == cur_non_terminal)
            .expect("Current non-terminal not found in the list");
        if next_index + 1 < non_terminal_vecs.len() {
            next_non_terminal = non_terminal_vecs[next_index + 1].clone(); // 下一个非终结符
            next_prog = 0;
        } else {
            // 如果已经是最后一个非终结符，返回当前值
            panic!("No more non-terminals")
        }

    } else {
        next_non_terminal = cur_non_terminal.clone();
        next_prog = cur_prog + 1;
    }

    (next_non_terminal, next_prog)
}