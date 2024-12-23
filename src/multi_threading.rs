pub mod search {
    use std::thread;
    use std::sync::{
        Arc, OnceLock
    };
    use crate::collect_callings::collect_callings::collect_callings_of_fun;
    use crate::{base, collect_callings};
    use crate::base::function::{GetValueError, NamedExecutable};
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
    use std::{collections::HashMap, fmt::Debug, hash::Hash};
    const MAX_THREADS: usize = 8;
    // 高并发 HashMap
    type ConcurrentHashSet<K> = scc::HashIndex<K, ()>;
    type ExpQueue<Identifier, Values> = scc::Queue<Exp<Identifier, Values>>;
    type CounterExamples<Identifier, Values, Types> = Vec<HashMap<Identifier, (Types, Values)>>;
    type Message<Identifier, Values> = Exp<Identifier, Values>;
    fn sync_search<
        'a,
        Identifier: Eq + Hash + Clone + VarIndex + Debug + Send + Sync + 'static,
        Values: Eq + Copy + Debug + Hash + 'static + Send + Sync + ConstraintPassesValue,
        Types: Eq + Copy + Debug + Send + 'static + Send + Sync,
        Context: Scope<Identifier, Types, Values, FunctionVar> + Send + Sync,
        FunctionVar: PositionedExecutable<Identifier, Values, Values> + FromBasicFun<'a, Identifier, Values, Types, Context>
    > (
        synth_fun: &'a SynthFun<Identifier, Values, Types>,
        constraints: &Vec<Constraint<Identifier, Values>>,
        scope: &'a Context
    ) -> Result<Exp<Identifier, Values>, String> {
        let mut counter_examples: CounterExamples<Identifier, Values, Types> = Vec::new();
        // 收集所有对 f 的调用
        let (new_constraint, callings_map) = collect_callings_of_fun(
            synth_fun.get_name(),
            constraints);
        let callings_map_ref = &callings_map;
        loop {
            let mut prev_results = ConcurrentHashSet::<Vec<Vec<Values>>>::new();
            let available_exps = ExpQueue::<Identifier, Values>::default();
            let available_exps_ref = &available_exps;
            let prev_results_ref = &prev_results;
            let (tx, rx) = spmc::channel::<Message<Identifier, Values>>();
            // 由于闭包的 move 关键字不能指定 move 哪些变量，这里手动让它 move 一个引用
            let counter_examples_ref = &counter_examples;
            let scope_ref = &scope;
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
                                while let Ok(exp) = rx.recv() {
                                    // 注意这里 rx.recv 是 block 的
                                    if program_passes_tests_ref.get().is_some() {
                                        break;
                                    }
                                    let mut pass_test = true;
                                    // 在每组测试中，所有对 f 的调用产生的值
                                    let mut values_on_each_test_and_each_call: Vec<Vec<Values>> = Vec::new();
                                    // let mut scope_with_test_values = Scope
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
                                        for (id, exp) in callings_map_ref {
                                            let args = match exp {
                                                Exp::Apply(_, args) => args,
                                                _ => panic!("Callings map should only contain Apply expressions")
                                            };
                                            // let args_results  
                                            let res = synth_fun.execute_exp_in_context(
                                                args,
                                                Some(*scope_ref), 
                                                exp);
                                            // let res = exp.instantiate_and_execute(
                                            //     synth_fun, 
                                            //     Some(*scope_ref),
                                            //     &exp,
                                            //     // 这里是因为如果有 f (f 1) 出现，会被整理成 a = f 1, b = f a 这样的形式，因此可能用到前面计算好的结果
                                            //     |id| match values_on_each_call_map.get(&id) {
                                            //         Some(v) => Ok(Either::Left(*v)),
                                            //         None => match test.get(&id) {
                                            //             Some((_, v)) => Ok(Either::Left(*v)),
                                            //             None => Err(GetValueError::VarNotDefinedWhenGet("Var not defined when get in test conunter examples".to_string()))
                                            //             }
                                            //     }
                                            // ).unwrap();
                                            values_on_each_call_map.insert(id.clone(), res);
                                        }
                                        for constaint in constraints {
                                            let res = constaint.get_body().execute_in_optional_context(
                                                Some(*scope_ref),
                                                |id| {
                                                    match values_on_each_call_map.get(&id) {
                                                        Some(v) => Ok(Either::Left(*v)),
                                                        None => match test.get(&id) {
                                                            Some((_, v)) => Ok(Either::Left(*v)),
                                                            None => Err(GetValueError::VarNotDefinedWhenGet("Var not defined when get in test conunter examples".to_string()))
                                                        }
                                                    }
                                                }
                                            ).unwrap();
                                            if !res.is_pass() {
                                                pass_test = false;
                                            }
                                        }
                                        let values_on_each_call = callings_map_ref.iter().map(|(id, _)| values_on_each_call_map.get(id).unwrap().clone()).collect::<Vec<_>>();
                                        values_on_each_test_and_each_call.push(values_on_each_call);
                                    }
                                    // 如果测试通过，就写在 program_passes_tests_ref 中
                                    if pass_test {
                                        let _ = program_passes_tests_ref.set(exp);  // 注意，假如其他线程已经找到了解，这里的 set 会被忽略，这正是我们预期的行为
                                        break;
                                    }
                                    // 否则，检查当前的 f 是否需要被等价性消减
                                    match prev_results_ref.insert(values_on_each_test_and_each_call, ()) {
                                        Ok(_) => {
                                            // 如果插入成功，说明结果没有出现过
                                            // 将 exp 写入可用表达式组之中
                                            available_exps_ref.push(exp);
                                        }
                                        Err(_) => {
                                            // 如果插入失败，说明结果出现过，不用写入
                                            ()
                                        }
                                    }
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