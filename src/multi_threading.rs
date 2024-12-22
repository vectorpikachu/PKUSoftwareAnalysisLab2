pub mod search {
    use std::thread;
    use std::sync::{
        Arc, OnceLock
    };
    use crate::base;
    use crate::base::function::GetValueError;
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
    type CounterExamples<Identifier, Values, Types> = Vec<HashMap<Identifier, (Types, Values)>>;
    type Message<Identifier, Values> = Exp<Identifier, Values>;
    fn sync_search<
        Identifier: Eq + Hash + Clone + VarIndex + Debug + Send + Sync + 'static,
        Values: Eq + Copy + Debug + Hash + 'static + Send + Sync + ConstraintPassesValue,
        Types: Eq + Copy + Debug + Send + 'static + Send + Sync,
        Context: Scope<Identifier, Types, Values, FunctionVar> + Send + Sync,
        FunctionVar: PositionedExecutable<Identifier, Values, Values> + FromBasicFun<Identifier, Values, Types, Context>
    > (
        synth_fun: &SynthFun<Identifier, Values, Types>,
        constraints: &Vec<Constraint<Identifier, Values>>,
        scope: Context
    ) -> Result<Exp<Identifier, Values>, String> {
        let mut counter_examples: CounterExamples<Identifier, Values, Types> = Vec::new();
        loop {
            let mut prev_results = ConcurrentHashSet::<Vec<Values>>::new();
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
                                let mut results = Vec::<Values>::new();
                                while let Ok(exp) = rx.recv() {
                                    // 注意这里 rx.recv 是 block 的
                                    if program_passes_tests_ref.get().is_some() {
                                        break;
                                    }
                                    let mut pass_test = true;
                                    for test in counter_examples_ref {
                                        for constaint in constraints {
                                            let res = constaint.instantiate_and_execute(
                                                synth_fun,
                                                Some(scope_ref),
                                                &exp,
                                                |id| match test.get(&id) {
                                                    Some((_, v)) => Ok(Either::Left(*v)),
                                                    None => Err(GetValueError::VarNotDefinedWhenGet("Var not defined when get in test conunter examples".to_string()))
                                                }
                                            ).unwrap();
                                            if !res.is_pass() {
                                                pass_test = false;
                                            }
                                            results.push(res);
                                        }
                                    }
                                    if pass_test {
                                        let _ = program_passes_tests_ref.set(exp);  // 注意，假如其他线程已经找到了解，这里的 set 会被忽略，这正是我们预期的行为
                                        break;
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