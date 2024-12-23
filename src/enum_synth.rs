//! 实现最基础的枚举合成器

use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::Peekable;
use std::mem;
use std::sync::Arc;

use either::Either;
use either::Either::Left;
use either::Either::Right;
use sexp::Sexp;
use z3::Config;
use z3_sys::Z3_mk_config;
use z3_sys::Z3_mk_context;
use z3_sys::Z3_context;

use crate::base::function::ExecError;
use crate::base::function::GetValueError;
use crate::base::function::PositionedExecutable;
use crate::base::function::VarIndex;
use crate::base::language::Constraint;
use crate::base::language::ConstraintPassesValue;
use crate::base::language::DeclareVar;
use crate::base::language::DefineFun;
use crate::base::language::Exp;
use crate::base::language::FromBasicFun;
use crate::base::language::Rule;
use crate::base::language::SynthFun;
use crate::base::language::Terms;
use crate::base::language::Type;
use crate::base::logic::LogicTag;
use crate::base::scope::Scope;
use crate::lia_builtin;
use crate::lia_logic::lia;

use crate::parser::parser::parse_logic;
use crate::parser::parser::MutContextSexpParser;
use crate::parser::rc_function_var_context::Command;
use crate::z3_solver;
use crate::z3_solver::GetZ3Type;
use crate::z3_solver::GetZ3Value;
use crate::z3_solver::NewPrimValues;

/// 设计一个枚举合成器
pub fn enum_synth_fun(read_file: &str) -> Either<String, String> {
    let cmds = "(\n".to_string() + read_file + "\n)";
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

    let logic_result = parse_logic(&sexps[0]);

    match logic_result {
        Ok(logic_tag) => {
            match logic_tag {
                LogicTag::LIA => {
                    // 调用 LIA 的 enum_synth_for_lia
                    return enum_synth_for_lia(&sexps[1..]);
                }
                LogicTag::BV => {
                    // 调用 BV 的 enum_synth_for_bv
                }
            }
        }
        Err(e) => {
            panic!("Error: {:?}", e);
        }
    }

    return Right("No solution found".to_string());
}


fn get_z3_ctx_ptr(context: &z3::Context) -> *mut Z3_context {
    // 使用 unsafe 和 transmute 强制转换为指针类型
    unsafe { mem::transmute::<&z3::Context, *mut Z3_context>(context) }
}

fn basic_search<
    'a,
    Identifier: Eq + Hash + Clone + VarIndex + Debug,
    Values: Eq + Copy + Debug + Hash + ConstraintPassesValue + GetZ3Value<'a> + NewPrimValues,
    Types: Eq + Copy + Debug + Hash + GetZ3Type<'a> + Type,
    Context: Scope<Identifier, Types, Values, FunctionVar> + Clone,
    FunctionVar: PositionedExecutable<Identifier, Values, Values>
        + FromBasicFun<Identifier, Values, Types, Context>
        + Clone,
>(
    synth_fun: &SynthFun<Identifier, Values, Types>,
    constraints: &Vec<Constraint<Identifier, Values>>,
    defines: &Vec<Arc<DefineFun<Identifier, Values, Types, FunctionVar, Context>>>,
    declare_vars: &Vec<DeclareVar<Identifier, Types>>,
    scope: &Context,
    z3_ctx: &'a mut z3::Context,
) -> Result<Exp<Identifier, Values>, String> {
    let mut prog_size = 1;
    // 必须记录所有已经存在的表达式
    let mut visited_exprs = HashSet::new();
    let mut candidate_exprs: HashMap<i32, HashMap<Identifier, Vec<Exp<Identifier, Values>>>> =
        HashMap::new();
    candidate_exprs.insert(prog_size, HashMap::new());
    for rule in synth_fun.get_all_rules() {
        candidate_exprs
            .get_mut(&prog_size)
            .unwrap()
            .insert(rule.0.clone(), vec![]);
        for production in rule.1 {
            let now_expr = production.get_body().clone();
            if !check_terminal::<Identifier, Values, Types>(&now_expr, synth_fun) {
                continue;
            }
            if visited_exprs.contains(&now_expr) {
                continue;
            }
            visited_exprs.insert(now_expr.clone());
            candidate_exprs
                .get_mut(&prog_size)
                .unwrap()
                .get_mut(rule.0)
                .unwrap()
                .push(now_expr);
        }
    }

    let mut counter_examples: Vec<HashMap<Identifier, (Types, Values)>> = Vec::new();
    let arc_context = Arc::new(scope.clone());

    loop {
        let now_exprs = get_availabe_progs(
            &synth_fun,
            &candidate_exprs,
            prog_size,
            synth_fun.get_return_type(),
        );
        for expr in now_exprs {
            if check_terminal::<Identifier, Values, Types>(&expr, &synth_fun) {
                let now_prog = synth_fun.exp_to_basic_fun(Some(arc_context.clone()), &expr);
                // 首先计算是否满足先前返回的反例
                // 反例是一个 HashMap<String, (Type, Value)>

                let mut pass_test = true;
                if !counter_examples.is_empty() {
                    for counter_example in counter_examples.iter() {
                        for constraint in constraints {
                            let passed = constraint.get_body().instantiate_and_execute(
                                &synth_fun,
                                Some(Arc::new(scope.clone())),
                                &expr.clone(),
                                |id| match counter_example.get(id) {
                                    Some((_, v)) => Ok(Either::Left(*v)),
                                    None => Err(GetValueError::VarNotDefinedWhenGet(
                                        "Var not defined when get in test conunter examples"
                                            .to_string(),
                                    )),
                                },
                            );
                            let is_pass = match passed {
                                Ok(v) => v.is_pass(),
                                Err(ExecError::DivZero) => false,
                                _ => panic!("Error: {:?}", passed),
                            };
                            if !is_pass {
                                pass_test = false;
                                break;
                            }
                        }
                    }
                }

                if !pass_test {
                    continue;
                }

               
               // 直接上指针了
               // ? 指针！
               unsafe {
                  let ptr = get_z3_ctx_ptr(&z3_ctx);
                  *ptr = Z3_mk_context(Z3_mk_config());
               };

               let mut solver =
                    z3_solver::Z3Solver::new(defines, declare_vars, synth_fun, constraints, z3_ctx);
                
                let res = solver.get_counterexample(&now_prog);

                println!("res: {:?}", res);

                match res {
                    Ok(either_val) => match either_val {
                        Left(v) => {
                            counter_examples.push(v);
                        }
                        Right(e) => {
                            println!("The exp satisifies all constraints: {:?}", e);
                            return Ok(expr);
                        }
                    },
                    Err(e) => {
                        panic!("Error: {:?}", e);
                    }
                }
            }
        }

        prog_size += 1;
        if prog_size > 10 {
            break;
        }
        enumerate_exprs(
            &synth_fun,
            &mut candidate_exprs,
            prog_size,
            &mut visited_exprs,
        );
    }
    return Err("No solution found".to_string());
}

/// 对于 LIA 的枚举合成器
fn enum_synth_for_lia(sexps: &[Sexp]) -> Either<String, String> {
    let mut ctx = lia_builtin::lia_builtin::get_empty_context_with_builtin();
    let mut defines = Vec::new();
    let mut declare_vars = Vec::new();
    let mut synth_func = None;
    let mut constraints: Vec<Constraint<String, lia::Values>> = Vec::new();
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

    let mut z3_ctx = z3::Context::new(&Config::new());
    let res_exp = basic_search(
        &synth_fun,
        &constraints,
        &defines,
        &declare_vars,
        &ctx,
        &mut z3_ctx,
    );

    match res_exp {
        Ok(e) => {
            println!("Found a solution: {}", e.to_string());
            return Left(e.to_string());
        }
        Err(e) => {
            println!("Error: {:?}", e);
            return Right(format!("Error: {:?}", e));
        }
    }
}

fn check_terminal<
    Identifier: Eq + Hash + Clone + VarIndex + Debug,
    Values: Eq + Copy + Debug + Hash + ConstraintPassesValue,
    Types: Eq + Copy + Debug + Hash,
>(
    exp: &Exp<Identifier, Values>,
    synth_fun: &SynthFun<Identifier, Values, Types>,
) -> bool {
    match exp {
        Exp::Value(v) => match v {
            Terms::PrimValue(_pv) => true,
            Terms::Var(v) => synth_fun.is_terminal(v),
        },
        Exp::Apply(func, args) => {
            if synth_fun.is_terminal(func) {
                for arg in args {
                    if !check_terminal::<Identifier, Values, Types>(arg, synth_fun) {
                        return false;
                    }
                }
                return true;
            } else {
                return false;
            }
        }
    }
}

/// 枚举 prog_size 的所有表达式
/// 比如说 Expr -> Expr + Expr, 那么就去
/// candidate_exprs[x1][Expr] 和 candidate_exprs[x2][Expr] 枚举
/// x1 + x2 = prog_size
/// 如果有 k 个非终结符, 则 x1 + x2 + ... + xk = prog_size
/// 所有的结果会被写入 candidate_exprs[prog_size] 中
fn enumerate_exprs<
    Identifier: Eq + Hash + Clone + VarIndex + Debug,
    Values: Clone + Debug + Copy + Eq + Hash,
    Types: Eq + Copy + Debug + Hash,
>(
    synth_fun: &SynthFun<Identifier, Values, Types>,
    candidate_exprs: &mut HashMap<i32, HashMap<Identifier, Vec<Exp<Identifier, Values>>>>,
    prog_size: i32,
    visited_exprs: &mut HashSet<Exp<Identifier, Values>>,
) {
    let non_terminals = synth_fun
        .get_all_rules()
        .keys()
        .map(|x| x.clone())
        .collect::<HashSet<_>>();

    for id_rules in synth_fun.get_all_rules() {
        let id = id_rules.0;
        let rules = id_rules.1;
        for rule in rules {
            let result = dfs_one_non_terminal_rule(
                rule,
                &non_terminals,
                candidate_exprs,
                prog_size,
                visited_exprs,
            );
            candidate_exprs
                .entry(prog_size)
                .or_insert(HashMap::new())
                .entry(id.clone())
                .or_insert(Vec::new())
                .extend(result);
        }
    }
}

/// 得到候选程序中可用的表达式
fn get_availabe_progs<
    Identifier: Eq + Hash + Clone + VarIndex + Debug,
    Values: Eq + Copy + Debug + Hash + ConstraintPassesValue,
    Types: Eq + Copy + Debug + Hash,
>(
    synth_fun: &SynthFun<Identifier, Values, Types>,
    candidate_exprs: &HashMap<i32, HashMap<Identifier, Vec<Exp<Identifier, Values>>>>,
    prog_size: i32,
    ty: &Types,
) -> Vec<Exp<Identifier, Values>> {
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

/// 要求 occurrences_mut_pointer 中的指针指向的是 actual_rule 的 body 的子节点
unsafe fn dfs_one_non_terminal_rule_aux<
    Identifier: Eq + Clone + Hash + Debug,
    Values: Eq + Copy + Debug + Hash,
>(
    actual_rule: &mut Rule<Identifier, Values>,
    // non_terminals: &HashSet<Identifier>,
    candidate_exprs: &HashMap<i32, HashMap<Identifier, Vec<Exp<Identifier, Values>>>>,
    results: &mut Vec<Exp<Identifier, Values>>,
    remaining_size: i32,
    remaining_non_terminals: i32, // 表达式中还余的非终结符个数
    occurrences_mut_pointer: &HashMap<Identifier, Vec<*mut Exp<Identifier, Values>>>,
    mut identifier_iter: Peekable<impl Iterator<Item = Identifier> + Clone>,
    pointer_iter: Option<std::slice::Iter<*mut Exp<Identifier, Values>>>, // 下一个要修改的是 cur_enum_non_terminal 的哪个引用，为空表示从当前非终结符的第一个引用开始
    visited_exprs: &mut HashSet<Exp<Identifier, Values>>,
) {
    if remaining_size == 0 {
        if remaining_non_terminals == 0 {
            // 所有非终结符都替换完毕，将结果加入到 results 中
            let res = actual_rule.get_body().clone();
            if visited_exprs.contains(&res) {
                return;
            }
            visited_exprs.insert(res.clone());
            results.push(res);
        }
    }
    let cur_non_terminals = match identifier_iter.peek() {
        Some(id) => id.clone(),
        None => return, // 非终结符已经遍历完成，而 remaining_size 非零，直接返回
    };
    let cur_occurrences = occurrences_mut_pointer.get(&cur_non_terminals).unwrap();
    let mut pointer_iter = match pointer_iter {
        Some(iter) => iter,
        None => cur_occurrences.iter(),
    };
    let cur_enum_loc = match pointer_iter.next() {
        None => {
            // 当前非终结符的所有引用都已经替换完毕，用下一个非终结符继续替换
            identifier_iter.next().unwrap();
            dfs_one_non_terminal_rule_aux(
                actual_rule,
                candidate_exprs,
                results,
                remaining_size,
                remaining_non_terminals,
                occurrences_mut_pointer,
                identifier_iter,
                None,
                visited_exprs,
            );
            return;
        }
        Some(loc) => loc,
    };
    // 否则
    for sz in 1..=remaining_size {
        // 选择当前非终结符的 size
        if let Some(cur_candidates) = candidate_exprs.get(&sz) {
            if let Some(cur_candidates) = cur_candidates.get(&cur_non_terminals) {
                for candidate in cur_candidates {
                    // 替换当前的引用
                    unsafe {
                        **cur_enum_loc = candidate.clone();
                    }
                    dfs_one_non_terminal_rule_aux(
                        actual_rule,
                        candidate_exprs,
                        results,
                        remaining_size - sz,
                        remaining_non_terminals - 1,
                        occurrences_mut_pointer,
                        identifier_iter.clone(),
                        Some(pointer_iter.clone()),
                        visited_exprs,
                    );
                }
            }
        }
    }
}

/// 现在比如 有一个 非终结符 `Start`.
/// 有一个产生式 `Start -> Start + Start`
/// 那么 `non_terminals["Start"] = vec![1, 2]`
/// 1,2 分别表示 第一个 `Start` 处的引用和第二个处的引用
/// 那么我们就应该
/// `(x1, x2)` 中的所有可能拼在一起把引用给 `actual_rule`
/// 然后得到 `actual_rule.get_body()` 就得到了一个全是终结符的合法程序
/// 此处应该写一个 DFS 来枚举所有的可能组合
fn dfs_one_non_terminal_rule<
    Identifier: Eq + Clone + Hash + Debug,
    Values: Eq + Copy + Debug + Hash,
>(
    rule: &Rule<Identifier, Values>,
    non_terminals: &HashSet<Identifier>,
    candidate_exprs: &HashMap<i32, HashMap<Identifier, Vec<Exp<Identifier, Values>>>>,
    total_size: i32,
    visited_exprs: &mut HashSet<Exp<Identifier, Values>>,
) -> Vec<Exp<Identifier, Values>> {
    let mut rule_to_modify = rule.clone(); // 复制一份进行操作
    let occurrences = rule_to_modify
        .get_counts(|id| non_terminals.contains(&id))
        .into_iter()
        .map(|(id, ocr)| {
            (
                id,
                ocr.into_iter()
                    .map(|x| x as *mut Exp<Identifier, Values>)
                    .collect(),
            )
        })
        .collect::<HashMap<Identifier, Vec<*mut Exp<Identifier, Values>>>>();
    let total_non_terminals_in_rule: i32 =
        occurrences.iter().map(|(_, ocr)| ocr.len() as i32).sum();
    let mut results = Vec::new();
    unsafe {
        dfs_one_non_terminal_rule_aux(
            &mut rule_to_modify,
            candidate_exprs,
            &mut results,
            total_size,
            total_non_terminals_in_rule,
            &occurrences,
            occurrences.keys().cloned().peekable(),
            None,
            visited_exprs,
        );
    }
    results
}

impl ToString for lia::Types {
    fn to_string(&self) -> String {
        match self {
            lia::Types::Int => "Int".to_string(),
            lia::Types::Bool => "Bool".to_string(),
            lia::Types::Function => "Function".to_string(), // 在 SMT-LIB 中未直接支持，可以做自定义扩展
        }
    }
}

impl ToString for lia::Values {
    fn to_string(&self) -> String {
        match self {
            lia::Values::Int(v) => v.to_string(),
            lia::Values::Bool(v) => v.to_string(),
        }
    }
}

impl<Identifier: Clone + Eq + ToString, PrimValues: Copy + Eq + ToString> ToString
    for Terms<Identifier, PrimValues>
{
    fn to_string(&self) -> String {
        match self {
            Terms::Var(var) => var.to_string(),
            Terms::PrimValue(value) => value.to_string(),
        }
    }
}

impl<Identifier: Clone + Eq + ToString, PrimValues: Copy + Eq + ToString> ToString
    for Exp<Identifier, PrimValues>
{
    fn to_string(&self) -> String {
        match self {
            Exp::Value(term) => term.to_string(),
            Exp::Apply(func, args) => {
                let func_str = func.to_string();
                let args_str = args
                    .iter()
                    .map(|arg| arg.to_string())
                    .collect::<Vec<String>>()
                    .join(" ");
                format!("({} {})", func_str, args_str)
            }
        }
    }
}

impl ToString for SynthFun<String, lia::Values, lia::Types> {
    fn to_string(&self) -> String {
        let name = self.get_name();
        let args = self
            .get_args()
            .iter()
            .map(|(arg_name, arg_type)| format!("({} {})", arg_name, arg_type.to_string()))
            .collect::<Vec<String>>()
            .join(" ");

        format!(
            "(define-fun {} ({}) {} ",
            name,
            args,
            self.get_return_type().to_string()
        )
    }
}
