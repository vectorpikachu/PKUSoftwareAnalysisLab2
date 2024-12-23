pub mod search {
    use std::arch::x86_64::_mm_permutevar_pd;
    use std::borrow::Borrow;
    use std::task::Context;
    use std::thread;
    use std::sync::{
        Arc, OnceLock
    };
    use crate::collect_callings::collect_callings::collect_callings_of_fun;
    use crate::{base, collect_callings, z3_solver};
    use crate::base::function::{ExecError, GetValueError, NamedExecutable};
    use crate::base::language::{ConstraintPassesValue, FromBasicFun};
    use base::{
        language::{
            SynthFun,
            Constraint,
            Exp,
            Rule,
        },
        function::{
            VarIndex,
            PositionedExecutable
        },
        scope::Scope
    };
    use either::Either;
    use z3::Config;
    use std::{collections::HashMap, fmt::Debug, hash::Hash};
    const MAX_THREADS: usize = 8;
    // 高并发 HashMap
    type ConcurrentHashSet<K> = scc::HashIndex<K, ()>;
    type ConcurrentHashMap<K, V> = scc::HashMap<K, V>;
    type ConcurrentHashIndex<K, V> = scc::HashIndex<K, V>;
    type ExpQueue<Identifier, Values> = scc::Queue<Exp<Identifier, Values>>;
    type CounterExamples<Identifier, Values, Types> = Vec<HashMap<Identifier, (Types, Values)>>;
    type Message<Identifier, Values> = (Identifier, Exp<Identifier, Values>);
    fn sync_search<
        Identifier: Eq + Hash + Clone + VarIndex + Debug + Send + Sync + 'static,
        Values: Eq + Copy + Debug + Hash + 'static + Send + Sync + ConstraintPassesValue,
        Types: Eq + Copy + Debug + Send + 'static + Send + Sync,
        Context: Scope<Identifier, Types, Values, FunctionVar> + Send + Sync + 'static,
        FunctionVar
    > (
        synth_fun: &SynthFun<Identifier, Values, Types>,
        constraints: &Vec<Constraint<Identifier, Values>>,
        scope: Arc<Context>,
        z3_solver: &z3_solver::Z3Solver<Identifier>,
    ) -> Result<Exp<Identifier, Values>, String> 
    where 
        for <'a> FunctionVar: PositionedExecutable<Identifier, Values, Values> + FromBasicFun <'a, Identifier, Values, Types, Context> + Copy
    {
        let mut counter_examples: CounterExamples<Identifier, Values, Types> = Vec::new();
        // 收集所有对 f 的调用
        let (new_constraint, callings_map) = collect_callings_of_fun(
            synth_fun.get_name(),
            constraints);
        let callings_map_ref = &callings_map;
        let new_constraint_ref = &new_constraint;
        let scope_arc_ref = &scope;
        // 每次发现新的反例
        loop {
            // 依次枚举程序大小
            // 该层程序中，可以留待未来使用的
            // 这两个变量只由主线程使用
            let mut prog_size = 1;
            let mut candidate_exprs: HashMap<i32, ConcurrentHashIndex<Identifier, ExpQueue::<Identifier, Values>>> = HashMap::new();
            candidate_exprs.insert(prog_size, ConcurrentHashIndex::new());

            // 对于不同的非终结符，存储出现过的可观测结果
            let prev_results: ConcurrentHashIndex<Identifier, ConcurrentHashSet<Vec<Vec<Values>>>> = ConcurrentHashIndex::new();
            // 对于当前层不同的非终结符，存储可用的表达式。每次切换到更高层时，主线程把它移动到 candidate_exprs 然后清空
            let available_exps: ConcurrentHashIndex<Identifier, ExpQueue::<Identifier, Values>> = ConcurrentHashIndex::new();
            let available_exps_ref = &available_exps;
            let prev_results_ref = &prev_results;
            let candidate_exprs_ref = &candidate_exprs;
            let (tx, rx) = spmc::channel::<Message<Identifier, Values>>();
            // 由于闭包的 move 关键字不能指定 move 哪些变量，这里手动让它 move 一个引用
            let counter_examples_ref = &counter_examples;
            let program_passes_tests: OnceLock<Exp<Identifier, Values>> = OnceLock::new();
            let program_passes_tests_ref = &program_passes_tests;
            thread::scope(
                |s| {
                    let mut threads = Vec::new();
                    for _ in 1..MAX_THREADS {
                        let rx = rx.clone();

                        // 子线程负责验证所有的 counter examples
                        threads.push(s.spawn(
                            move || {
                                while let Ok((name_of_non_terminal, exp)) = rx.recv() {
                                    // 注意这里 rx.recv 是 block 的
                                    if program_passes_tests_ref.get().is_some() {
                                        break;
                                    }
                                    let scope_ref: &Context = scope_arc_ref.borrow();
                                    let mut pass_test = true;
                                    let mut valid_program = true;   // 如果出现除零等问题，说明程序不合法，直接丢弃
                                    // 在每组测试中，所有对 f 的调用产生的值
                                    let mut values_on_each_test_and_each_call: Vec<Vec<Values>> = Vec::new();
                                    for test in counter_examples_ref {
                                        let mut values_on_each_call_map = HashMap::<Identifier, Values>::new();
                                        // let values_on_each_call_map = callings_map_ref.iter().map(
                                        //     |(id, exp)| {
                                        //         (id, 
                                        //             exp.instantiate_and_execute(
                                        //             synth_fun, 
                                        //             Some(scope_ref),
                                        //             &exp,
                                        //             |id| match test.get(&id) {
                                        //                 Some((_, v)) => Ok(Either::Left(*v)),
                                        //                 None => Err(GetValueError::VarNotDefinedWhenGet("Var not defined when get in test conunter examples".to_string()))
                                        //             }
                                        //             ).unwrap()
                                        //         )
                                        //     }
                                        // ).collect::<HashMap<_, _>>();
                                        for (id, cal_exp) in callings_map_ref {
                                            let res = cal_exp.instantiate_and_execute(
                                                synth_fun, 
                                                Some(scope_ref), 
                                                &exp, 
                                                |id| {
                                                    // 这里是因为如果有 f (f 1) 出现，会被整理成 a = f 1, b = f a 这样的形式，因此可能用到前面计算好的结果
                                                    // or 是短路的，因此优先取 test 中的值
                                                    match values_on_each_call_map.get(&id).or(test.get(&id).map(|(_, v)| v)) {
                                                        Some(v) => Ok(Either::Left(*v)),
                                                        None => Err(GetValueError::VarNotDefinedWhenGet(format!("Var not defined when get in test conunter examples: {:?}", id)))
                                                    }
                                                }
                                            );
                                            match res {
                                                Ok(v) => {
                                                    values_on_each_call_map.insert(id.clone(), v);
                                                },
                                                Err(base::function::ExecError::DivZero) => {
                                                    pass_test = false;
                                                    valid_program = false;
                                                    break;
                                                },
                                                Err(e) => {
                                                    panic!("{:?}", e);
                                                }
                                            }
                                        }
                                        if !valid_program {
                                            break;
                                        }
                                        for constaint in new_constraint_ref {
                                            let res = constaint.get_body().execute_in_optional_context(
                                                Some(scope_ref),
                                                |id| {
                                                    match values_on_each_call_map.get(&id).or(test.get(&id).map(|(_, v)| v)) {
                                                        Some(v) => Ok(Either::Left(*v)),
                                                        None => Err(GetValueError::VarNotDefinedWhenGet(format!("Var not defined when get in test conunter examples: {:?}", id)))
                                                    }
                                                }
                                            );
                                            let res_value = match res {
                                                Ok(v) => v,
                                                Err(ExecError::DivZero) => {
                                                    pass_test = false;
                                                    valid_program = false;
                                                    break;
                                                },
                                                Err(e) => panic!("{:?}", e)
                                            };
                                            if !res_value.is_pass() {
                                                pass_test = false;
                                            }
                                        }
                                        if !valid_program {
                                            break;
                                        }
                                        let values_on_each_call = callings_map_ref.iter().map(|(id, _)| values_on_each_call_map.get(id).unwrap().clone()).collect::<Vec<_>>();
                                        values_on_each_test_and_each_call.push(values_on_each_call);
                                    }
                                    // 如果测试通过，就写在 program_passes_tests_ref 中
                                    if pass_test {
                                        let _ = program_passes_tests_ref.set(exp);  // 注意，假如其他线程已经找到解，这里的 set 可能会被忽略，这正是我们预期的行为
                                        break;
                                    }
                                    // 否则，检查当前的 f 是否需要被等价性消减
                                    prev_results_ref.peek_with(
                                        &name_of_non_terminal, 
                                        |_, v| match v.insert(values_on_each_test_and_each_call, ()) {
                                            Ok(_) => {
                                                // 如果插入成功，说明结果没有出现过
                                                // 将 exp 写入可用表达式组之中
                                                available_exps_ref.peek_with(
                                                    &name_of_non_terminal, 
                                                    |_, v| {
                                                        v.push(exp);
                                                    }
                                                ).unwrap(); // 这里假定所有非终结符对应的 hashmap 已经被主线程创建
                                            },
                                            // 如果插入失败，说明结果出现过，不用写入
                                            Err(_) => ()
                                        }
                                    ).unwrap()  // 这里假定所有非终结符对应的 hashmap 已经被主线程创建
                                }
                            }
                        ))

                        // 主线程负责生成新的 exp，以及找到通过所有测试的程序时发给 smt solver
                        
                    }
                }
            )
        }
    }
}