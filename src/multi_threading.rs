pub mod search {
    use std::arch::x86_64::_mm_permutevar_pd;
    use std::borrow::Borrow;
    use std::cell::{Cell, RefCell};
    use std::collections::HashSet;
    use std::rc::Rc;
    use std::sync::atomic::AtomicUsize;
    use std::task::Context;
    use std::thread;
    use std::sync::{
        Arc, OnceLock
    };
    use crate::collect_callings::collect_callings::collect_callings_of_fun;
    use crate::z3_solver::GetZ3Type;
    use crate::{base, collect_callings, parser, z3_solver};
    use crate::base::function::{ExecError, GetValueError, NamedExecutable};
    use crate::base::language::{ConstraintPassesValue, FromBasicFun, Type};
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
    use either::Either::{self, Left, Right};
    use once_cell::sync::OnceCell;
    use scc::ebr::Guard;
    use z3::Config;
    use std::{collections::HashMap, fmt::Debug, hash::Hash};
    const MAX_THREADS: usize = 8;
    // 高并发 HashMap
    type ConcurrentHashSet<K> = scc::HashIndex<K, ()>;
    type ConcurrentHashMap<K, V> = scc::HashMap<K, V>;
    type ConcurrentHashIndex<K, V> = scc::HashIndex<K, V>;
    type ExpQueue<Identifier, Values> = scc::Queue<Exp<Identifier, Values>>;
    type CounterExamples<Identifier, Values, Types> = scc::Queue<HashMap<Identifier, (Types, Values)>>;
    enum Message<Identifier: Clone + Eq, Values: Copy + Eq> {
        Halt,
        Exp(Identifier, Exp<Identifier, Values>),
    }
    type FunctionVar<'a, Identifier, Values> = parser::rc_function_var_context::RcFunctionVar<'a, Identifier, Values>;
    type AllCandidateExprs<Identifier, Values> = HashMap<i32, ConcurrentHashIndex<Identifier, ExpQueue::<Identifier, Values>>>;
    /// 得到候选程序中可用的表达式
    // fn get_availabe_progs<
    //     Identifier: Eq + Hash + Clone + VarIndex + Debug,
    //     Values: Eq + Copy + Debug + Hash + ConstraintPassesValue,
    //     Types: Eq + Copy + Debug + Hash,
    // >(
    //     synth_fun: &SynthFun<Identifier, Values, Types>,
    //     candidate_exprs: &HashMap<i32, HashMap<Identifier, Vec<Exp<Identifier, Values>>>>,
    //     prog_size: i32,
    //     ty: &Types,
    // ) -> Vec<Exp<Identifier, Values>> {
    //     let mut availabe_progs = Vec::new();
    //     let possible_progs = candidate_exprs.get(&prog_size);
    //     if possible_progs.is_none() {
    //         return availabe_progs;
    //     };
    //     for (id, v) in possible_progs.unwrap().iter() {
    //         if *synth_fun.get_type(id).unwrap() != *ty {
    //             continue;
    //         }
    //         for exp in v {
    //             availabe_progs.push(exp.clone());
    //         }
    //     }
    //     availabe_progs
    // }

    use std::iter::Peekable;
    /// 要求 occurrences_mut_pointer 中的指针指向的是 actual_rule 的 body 的子节点
    unsafe fn dfs_one_non_terminal_rule_aux<
        Identifier: Eq + Clone + Hash + Debug + 'static,
        Values: Eq + Copy + Debug + Hash + 'static,
    >(
        actual_rule: &mut Rule<Identifier, Values>,
        // non_terminals: &HashSet<Identifier>,
        candidate_exprs: &AllCandidateExprs<Identifier, Values>,
        results_handler: impl Fn(Exp<Identifier, Values>) -> bool + Clone,
        remaining_size: i32,
        remaining_non_terminals: i32, // 表达式中还余的非终结符个数
        occurrences_mut_pointer: &HashMap<Identifier, Vec<*mut Exp<Identifier, Values>>>,
        mut identifier_iter: Peekable<impl Iterator<Item = Identifier> + Clone>,
        pointer_iter: Option<std::slice::Iter<*mut Exp<Identifier, Values>>>, // 下一个要修改的是 cur_enum_non_terminal 的哪个引用，为空表示从当前非终结符的第一个引用开始
        // visited_exprs: &mut HashSet<Exp<Identifier, Values>>,
    ) -> bool {
        if remaining_size == 0 {
            if remaining_non_terminals == 0 {
                // 所有非终结符都替换完毕，将结果加入到 results 中
                let res = actual_rule.get_body().clone();
                // if visited_exprs.contains(&res) {
                //     return;
                // }
                // visited_exprs.insert(res.clone());
                return results_handler(res);
            }
        }
        let cur_non_terminals = match identifier_iter.peek() {
            Some(id) => id.clone(),
            None => return false, // 非终结符已经遍历完成，而 remaining_size 非零，直接返回
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
                return dfs_one_non_terminal_rule_aux(
                    actual_rule,
                    candidate_exprs,
                    results_handler,
                    remaining_size,
                    remaining_non_terminals,
                    occurrences_mut_pointer,
                    identifier_iter,
                    None,
                    // visited_exprs,
                )
            }
            Some(loc) => loc,
        };
        // 否则
        for sz in 1..=remaining_size {
            // 选择当前非终结符的 size
            if let Some(cur_candidates) = candidate_exprs.get(&sz) {
                if let Some(cur_candidates) = cur_candidates.get(&cur_non_terminals) {
                    let guard = Guard::new();
                    for candidate in cur_candidates.get().iter(&guard) {
                        // 替换当前的引用
                        unsafe {
                            **cur_enum_loc = candidate.clone();
                        }
                        let res = dfs_one_non_terminal_rule_aux(
                            actual_rule,
                            candidate_exprs,
                            results_handler.clone(),
                            remaining_size - sz,
                            remaining_non_terminals - 1,
                            occurrences_mut_pointer,
                            identifier_iter.clone(),
                            Some(pointer_iter.clone()),
                            // visited_exprs,
                        );
                        if !res {
                            return false;
                        }
                    }
                }
            }
        }
        return true;
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
        Identifier: Eq + Clone + Hash + Debug + 'static,
        Values: Eq + Copy + Debug + Hash + 'static,
    >(
        rule: &Rule<Identifier, Values>,
        non_terminals: &HashSet<Identifier>,
        candidate_exprs: &AllCandidateExprs<Identifier, Values>,
        total_size: i32,
        // visited_exprs: &mut HashSet<Exp<Identifier, Values>>,
        results_handler: impl Fn(Exp<Identifier, Values>) -> bool + Clone   // 这里的返回值表示是否停止枚举，返回 false 表示立刻停止
    ) {
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
        unsafe{
            dfs_one_non_terminal_rule_aux(
                &mut rule_to_modify,
                candidate_exprs,
                results_handler,
                total_size,
                total_non_terminals_in_rule,
                &occurrences,
                occurrences.keys().cloned().peekable(),
                None,
                // visited_exprs,
            );
        };
    }

    
    fn concurrent_search<
        'a,
        Identifier: Eq + Hash + Clone + VarIndex + Debug + Send + Sync + 'static,
        Values: Eq + Copy + Debug + Hash + 'static + Send + Sync + ConstraintPassesValue + z3_solver::GetZ3Value<'a> + z3_solver::NewPrimValues,
        Types: Eq + Copy + Debug + Send + 'static + Send + Sync + GetZ3Type<'a> + Type,
        Context: Scope<Identifier, Types, Values, FunctionVar<'a, Identifier, Values>> + Send + Sync + 'static,
        // FunctionVar
    > (
        synth_fun: &SynthFun<Identifier, Values, Types>,
        constraints: &Vec<Constraint<Identifier, Values>>,
        scope: Arc<Context>,
        z3_solver_generator: impl Fn() -> z3_solver::Z3Solver<'a, Identifier, Values>,
    ) -> Result<Exp<Identifier, Values>, String> 
    where 
    {
        let mut counter_examples: CounterExamples<Identifier, Values, Types> = CounterExamples::default();
        // 收集所有对 f 的调用
        let (new_constraint, callings_map) = collect_callings_of_fun(
            synth_fun.get_name(),
            constraints);
        let callings_map_ref = &callings_map;
        let new_constraint_ref = &new_constraint;
        let scope_arc_ref = &scope;
        // 每次发现新的反例
        loop {
            // 对于不同的非终结符，存储出现过的可观测结果
            let prev_results: ConcurrentHashIndex<Identifier, ConcurrentHashSet<Vec<Vec<Values>>>> = ConcurrentHashIndex::new();
            // 对于当前层不同的非终结符，存储可用的表达式。每次切换到更高层时，主线程把它移动到 candidate_exprs 然后清空
            let available_exps: ConcurrentHashIndex<Identifier, ExpQueue::<Identifier, Values>> = ConcurrentHashIndex::new();
            let available_exps_ref = &available_exps;
            let prev_results_ref = &prev_results;
            let (tx, rx) = spmc::channel::<Message<Identifier, Values>>();
            let tx_rc_ref_cell: Rc<RefCell<_>> = Rc::new(RefCell::new(tx));
            // 由于闭包的 move 关键字不能指定 move 哪些变量，这里手动让它 move 一个引用
            let counter_examples_ref = &counter_examples;
            let program_passes_tests: OnceCell<Exp<Identifier, Values>> = OnceCell::new();
            let program_passes_tests_ref = &program_passes_tests;

            // let all_tasks_done_flag: Arc<Cell<OnceCell<()>>> = Arc::new(Cell::new(OnceCell::new()));

            let processing_task: Arc<AtomicUsize> = Arc::new(AtomicUsize::new(0));  // 用于记录当前处理的任务数
            let processing_task_ref = &processing_task;
            if let Ok(result_exp) = thread::scope(
                |s| {
                    let mut threads = Vec::new();
                    for _ in 1..MAX_THREADS {
                        let rx = rx.clone();

                        // 子线程负责验证所有的 counter examples
                        threads.push(s.spawn(
                            move || {
                                while let Ok(msg) = rx.recv() {
                                    // 注意这里 rx.recv 是 block 的
                                    let (name_of_non_terminal, exp) = match msg {
                                        Message::Exp(name, exp) => (name, exp),
                                        _ => break
                                    };
                                    if program_passes_tests_ref.get().is_some() {
                                        break;
                                    }
                                    let scope_ref: &Context = scope_arc_ref.borrow();
                                    let mut pass_test = true;
                                    let mut valid_program = true;   // 如果出现除零等问题，说明程序不合法，直接丢弃
                                    // 在每组测试中，所有对 f 的调用产生的值
                                    let mut values_on_each_test_and_each_call: Vec<Vec<Values>> = Vec::new();

                                    // 将 exp 实例化为函数
                                    let f_instance = synth_fun.exp_to_basic_fun(Some(scope_arc_ref.clone()), &exp);
                                    let f_instance = FunctionVar::from_basic_fun(f_instance);
                                    let guard = Guard::new();
                                    for test in counter_examples_ref.iter(&guard) {
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
                                        for (id, call_exp) in callings_map_ref {
                                            let res = call_exp.execute_in_optional_context(
                                                Some(scope_ref),
                                                |id| {
                                                    if id == synth_fun.get_name() {
                                                        Ok(Either::Right(f_instance.clone()))
                                                    } else {
                                                        // 这里是因为如果有 f (f 1) 出现，会被整理成 a = f 1, b = f a 这样的形式，因此可能用到前面计算好的结果
                                                        // or 是短路的，因此优先取 test 中的值
                                                        match values_on_each_call_map.get(&id).or(test.get(&id).map(|(_, v)| v)) {
                                                            Some(v) => Ok(Either::Left(*v)),
                                                            None => Err(GetValueError::VarNotDefinedWhenGet(format!("Var not defined when get in test conunter examples: {:?}", id)))
                                                    }
                                                    }
                                                } 
                                            );
                                            // let res = cal_exp.instantiate_and_execute(
                                            //     synth_fun, 
                                            //     Some(scope_ref), 
                                            //     &exp, 
                                            //     |id| {
                                            //         // 这里是因为如果有 f (f 1) 出现，会被整理成 a = f 1, b = f a 这样的形式，因此可能用到前面计算好的结果
                                            //         // or 是短路的，因此优先取 test 中的值
                                            //         match values_on_each_call_map.get(&id).or(test.get(&id).map(|(_, v)| v)) {
                                            //             Some(v) => Ok(Either::Left(*v)),
                                            //             None => Err(GetValueError::VarNotDefinedWhenGet(format!("Var not defined when get in test conunter examples: {:?}", id)))
                                            //         }
                                            //     }
                                            // );
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
                                    ).unwrap();  // 这里假定所有非终结符对应的 hashmap 已经被主线程创建
                                    if processing_task_ref.clone().fetch_sub(1, std::sync::atomic::Ordering::Relaxed) == 1 {
                                        // 如果当前任务是最后一个任务，说明所有任务已经完成
                                        // let _ = all_tasks_done_flag_ref.set(());
                                    }
                                }
                            }
                        ))
                    }

                    let mut get_a_solution = false;
                    // 主线程负责生成新的 exp，以及找到通过所有测试的程序时发给 smt solver
                    while program_passes_tests.get().is_none() {
                        // 还没有找到解时

                        // 依次枚举程序大小
                        // 该层程序中，可以留待未来使用的
                        // 这两个变量只由主线程使用
                        let mut candidate_exprs: AllCandidateExprs<Identifier, Values> = HashMap::new();
                        let mut prog_size = 1;
                        candidate_exprs.insert(prog_size, ConcurrentHashIndex::new());
                        let all_rules = synth_fun.get_all_rules_with_non_terminals();
                        let all_non_terminals = all_rules.keys().cloned().collect::<HashSet<_>>();
                        for non_terminal in &all_non_terminals {
                            // 初始化一些信息
                            available_exps.insert((*non_terminal).clone(), ExpQueue::default());
                            prev_results.insert((*non_terminal).clone(), ConcurrentHashSet::new());
                        }
                        loop {
                            // let _ = all_tasks_done_flag.take();
                            // 我们假设所有线程处理程序大小是同步的，主线程会等待当前大小程序全部处理完，再处理下一个大小的程序
                            for non_terminal in &all_non_terminals {
                                // 初始化一些信息
                                available_exps.get(non_terminal).unwrap().update(ExpQueue::default());
                                prev_results.get(non_terminal).unwrap().update(ConcurrentHashSet::new());
                            }
                            // 枚举所有的规则
                            for (non_terminal, rules) in all_rules {
                                for rule in rules {
                                    // 枚举所有程序并加入到消息队列中
                                    dfs_one_non_terminal_rule(
                                        rule, 
                                        &all_non_terminals, 
                                        &candidate_exprs, 
                                        prog_size, 
                                        |res_exp| {
                                            if program_passes_tests_ref.get().is_some() {
                                                return false;
                                            }
                                            let tx = tx_rc_ref_cell.clone();
                                            let mut tx = tx.borrow_mut();
                                            processing_task_ref.clone().fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                                            tx.send(Message::Exp(non_terminal.clone(), res_exp)).unwrap();
                                            return true;
                                        }
                                    );
                                }
                            }
                            // 等待所有线程处理完毕。先使用 busy loop 有空再优化
                            while processing_task.load(std::sync::atomic::Ordering::Relaxed) != 0 && program_passes_tests_ref.get().is_none() {
                                // busy loop
                            }
                            // 如果找到通过测试的解
                            if let Some(exp) = program_passes_tests_ref.get() {
                                let mut solver = z3_solver_generator();
                                let now_prog = synth_fun.exp_to_basic_fun(Some(scope_arc_ref.clone()), &exp);
                                let res = solver.get_counterexample(&now_prog);
                                match res {
                                    Ok(either_val) => match either_val {
                                        Left(v) => {
                                            counter_examples.push(v);
                                            get_a_solution = true;
                                            break;
                                        }
                                        Right(e) => {
                                            println!("The exp satisifies all constraints: {:?}", e);
                                            return Ok(exp.clone());
                                        }
                                    },
                                    Err(e) => {
                                        panic!("Error: {:?}", e);
                                    }
                                }
                            }
                            if get_a_solution {
                                break;
                            }
                            // 否则，将本层得到的表达式加入可用表达式，进入下一层
                            // 将本层得到的表达式加入可用表达式
                            candidate_exprs.insert(prog_size, available_exps.clone());  // 这里本来不应该需要复制，但是由于 borrow checker 问题，先暂且这样做
                            prog_size += 1;
                        }
                        if get_a_solution {
                            break;
                        }
                    }
                    // 向所有线程发送停止消息
                    for _ in 0..MAX_THREADS {
                        let _ = tx_rc_ref_cell.borrow_mut().send(Message::Halt);
                    }
                    Err("Doesn't find a solution".to_string())
                    // 此处，所有的线程应当都 join 了
                }
            ) {
                return Ok(result_exp);
            }
        }
    }
}