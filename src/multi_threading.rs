pub mod search {
    use std::borrow::Borrow;
    use std::cell::{Cell, RefCell, UnsafeCell};
    use std::collections::HashSet;
    use std::mem::swap;
    use std::rc::Rc;
    use std::sync::atomic::{AtomicU32, AtomicUsize};
    use std::task::Context;
    use std::thread::{self, sleep};
    use std::sync::{
        Arc, Mutex, OnceLock, RwLock
    };
    use crate::collect_callings::collect_callings::collect_callings_of_fun;
    use crate::z3_solver::GetZ3Type;
    use crate::{base, collect_callings, parser, z3_solver};
    use crate::base::function::{ExecError, GetValueError, NamedExecutable};
    use crate::base::language::{BasicFun, ConstraintPassesValue, FromBasicFun, Type};
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
    use log::{debug, info, trace};
    use once_cell::sync::OnceCell;
    use scc::ebr::Guard;
    use z3::Config;
    use std::{collections::HashMap, fmt::Debug, hash::Hash};
    const MAX_THREADS: usize = 15;
    // 高并发 HashMap
    type ConcurrentHashSet<K> = scc::HashSet<K>;
    type ConcurrentHashMap<K, V> = scc::HashMap<K, V>;
    type ConcurrentHashIndex<K, V> = scc::HashIndex<K, V>;
    type ExpQueue<Identifier, Values> = scc::Queue<Exp<Identifier, Values>>;
    type CounterExamples<Identifier, Values, Types> = scc::Queue<HashMap<Identifier, (Types, Values)>>;
    enum Message<Identifier: Clone + Eq, Values: Copy + Eq> {
        Halt,
        Exp(Identifier, Exp<Identifier, Values>),
    }
    type FunctionVar<'a, Identifier, Values> = parser::rc_function_var_context::RcFunctionVar<'a, Identifier, Values>;
    type AllCandidateExprs<Identifier, Values> = HashMap<i32, ConcurrentHashMap<Identifier, ExpQueue::<Identifier, Values>>>;
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
        guard: &Guard,  // 用来保护 ExpQueue 的读取
    ) -> bool {
        // println!("{:?}", actual_rule.get_body());
        // println!("remaining_size: {}, remaining_non_terminals: {}", remaining_size, remaining_non_terminals);
        if remaining_size == 1 {
            if remaining_non_terminals == 0 {
                // 所有非终结符都替换完毕，将结果加入到 results 中
                let res = actual_rule.get_body().clone();
                return results_handler(res);
            }
            else {
                // println!("剩余非终结符不为 0，但是剩余大小为 1，直接返回");
                return true;    // 本次枚举没有得到新结果，可以继续枚举
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
                    guard
                    // visited_exprs,
                )
            }
            Some(loc) => loc,
        };
        // 否则
        for sz in 1..=remaining_size {
            // 选择当前非终结符的 size
            if let Some(cur_candidates) = candidate_exprs.get(&sz) {
                // if let Some(cur_candidates) = cur_candidates.get(&cur_non_terminals) {
                //     let guard = Guard::new();
                //     for candidate in cur_candidates.get().iter(&guard) {
                //         // 替换当前的引用
                //         unsafe {
                //             **cur_enum_loc = candidate.clone();
                //         }
                //         println!("sz: {}, cur_non_terminals: {:?}, candidate: {:?}", sz, cur_non_terminals, candidate);
                //         let res = dfs_one_non_terminal_rule_aux(
                //             actual_rule,
                //             candidate_exprs,
                //             results_handler.clone(),
                //             remaining_size - sz,
                //             remaining_non_terminals - 1,
                //             occurrences_mut_pointer,
                //             identifier_iter.clone(),
                //             Some(pointer_iter.clone()),
                //             // visited_exprs,
                //         );
                //         return res;
                //     }
                // }
                cur_candidates.read(&cur_non_terminals, 
                    |_, cur_candidates| {
                        for candidate in cur_candidates.iter(&guard) {
                            // println!("sz: {}, cur_non_terminals: {:?}, candidate: {:?}", sz, cur_non_terminals, candidate);
                            // 替换当前的引用
                            unsafe {
                                **cur_enum_loc = candidate.clone();
                            }
                            // println!("sz: {}, cur_non_terminals: {:?}, candidate: {:?}", sz, cur_non_terminals, candidate);
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
                                guard
                            );
                            if res == false {
                                // 如果返回 false，说明应当立刻终止枚举
                                return false;
                            }
                        }
                        return true;
                    }
                );
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
        let guard = Guard::new();
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
                &guard
            );
        };
    }
const ATOMIC_WRITE_ORDER: std::sync::atomic::Ordering = std::sync::atomic::Ordering::Release;
const ATOMIC_READ_ORDER: std::sync::atomic::Ordering = std::sync::atomic::Ordering::Acquire;
    fn sub_and_wake_when_zero(
        counter: &AtomicUsize,
        flag: &AtomicU32,
    ){
        let cur = counter.fetch_sub(1, ATOMIC_WRITE_ORDER);
        if cur == 1 {
            flag.fetch_add(1, ATOMIC_WRITE_ORDER);
            atomic_wait::wake_all(flag as *const AtomicU32);
        }
        trace!("当前任务数：{}", cur - 1);
    }

    fn clean_up_sub_threads<Identifier: Clone + Eq + Send + Sync, Values: Copy + Eq + Send + Sync>(
        num: usize,
        channel: &mut spmc::Sender<Message<Identifier, Values>>,
        lock: &RwLock<()>,
    ){
        for _ in 0..num {
            let _ = channel.send(Message::Halt);
        }
        // 等待所有线程退出
        let _wait = lock.write().unwrap();
        info!("所有子线程清理完成");
    }

    pub fn concurrent_search<
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
        z3_solver_call: 
            impl Fn(
                &BasicFun<Identifier, Values, Types, FunctionVar<'a, Identifier, Values>, Context>,
            ) -> Result<Either<HashMap<Identifier, (Types, Values)>, String>, String>,
    ) -> Result<Exp<Identifier, Values>, String> 
    where 
    {
        info!("开始搜索");
        let counter_examples: CounterExamples<Identifier, Values, Types> = CounterExamples::default();
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
            let prev_results: ConcurrentHashMap<Identifier, ConcurrentHashSet<Vec<Vec<Values>>>> = ConcurrentHashMap::new();
            // 对于当前层不同的非终结符，存储可用的表达式。每次切换到更高层时，主线程把它移动到 candidate_exprs 然后清空
            let available_exps: Arc<RwLock<ConcurrentHashMap<Identifier, ExpQueue::<Identifier, Values>>>> = Arc::new(RwLock::new(ConcurrentHashMap::new()));
            let available_exps_ref = &available_exps;
            let prev_results_ref = &prev_results;
            let (tx, rx) = spmc::channel::<Message<Identifier, Values>>();
            let tx_rc_ref_cell: Rc<RefCell<_>> = Rc::new(RefCell::new(tx));
            // 由于闭包的 move 关键字不能指定 move 哪些变量，这里手动让它 move 一个引用
            let counter_examples_ref = &counter_examples;
            let program_passes_tests: OnceCell<Exp<Identifier, Values>> = OnceCell::new();
            let program_passes_tests_ref = &program_passes_tests;

            // let all_tasks_done_flag: Arc<Cell<OnceCell<()>>> = Arc::new(Cell::new(OnceCell::new()));

            let processing_task: AtomicUsize = AtomicUsize::new(0);  // 用于记录当前处理的任务数
            let turn_is_finish: AtomicU32 = AtomicU32::new(0);  // 用于标注当前轮次是否结束

            let processing_task_ref = &processing_task;
            let turn_is_finish_ref = &turn_is_finish;

            let thread_exit_lock: RwLock<()> = RwLock::new(());
            let thread_exit_lock_ref = &thread_exit_lock;
            if let Ok(result_exp) = thread::scope(
                |s| {
                    let mut threads = Vec::new();
                    for _ in 1..MAX_THREADS {
                        let rx = rx.clone();
                        // 子线程负责验证所有的 counter examples
                        threads.push(s.spawn(
                            move || {
                                // 每个线程拿一个读锁，所有线程退出时才能安全的拿写锁
                                let available_exps_ref = available_exps_ref;
                                let turn_is_finish_ref = turn_is_finish_ref;
                                trace!("线程启动");
                                '_enum_program: while let Ok(msg) = rx.recv() {
                                    let _thread_survive_lock = thread_exit_lock_ref.read().unwrap();
                                    let available_exps_ref = available_exps_ref.read().unwrap();
                                    // 注意这里 rx.recv 是 block 的
                                    let (name_of_non_terminal, exp) = match msg {
                                        Message::Exp(name, exp) => (name, exp),
                                        Message::Halt => {
                                            break;
                                        }
                                    };
                                    trace!(
                                        "接收到消息：{:?}: {:?}",
                                        name_of_non_terminal,
                                        exp
                                    );
                                    if program_passes_tests_ref.get().is_some() {
                                        debug!(
                                            "其他线程找到解，跳过"
                                        );
                                        // // 注意，由于终止信号总是最后发出，因此使用 continue 保证消耗掉所有消息
                                        // sub_and_wake_when_zero(processing_task_ref, turn_is_finish_ref);
                                        break;
                                        // continue;
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
                                    '_enum_test: for test in counter_examples_ref.iter(&guard) {
                                        let mut values_on_each_call_map = HashMap::<Identifier, Values>::new();
                                        for (id, call_exp) in callings_map_ref {
                                            scope_ref.get_value(&Identifier::from_name("ite".to_string())).unwrap();
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
                                            match res {
                                                Ok(v) => {
                                                    values_on_each_call_map.insert(id.clone(), v);
                                                },
                                                Err(base::function::ExecError::DivZero) => {
                                                    pass_test = false;
                                                    valid_program = false;
                                                    break '_enum_test;  // 注意任务结束还有收尾，因此不能直接 continue '_enum_program;
                                                },
                                                Err(base::function::ExecError::TypeMismatch(_)) => {
                                                    // 如果在计算所有 f 调用的时候就发现类型错误，例如 (ite a 1 1) 1，说明该程序不合法，应该直接丢弃
                                                    // （也不能成为其他 f 的组成部分）
                                                    pass_test = false;
                                                    valid_program = false;
                                                    break '_enum_test;
                                                },
                                                Err(e) => {
                                                    panic!("{:?}", e);
                                                }
                                            }
                                        }
                                        // if !valid_program {
                                        //     break;
                                        // }
                                        let values_on_each_call = callings_map_ref.iter().map(|(id, _)| values_on_each_call_map.get(id).unwrap().clone()).collect::<Vec<_>>();
                                        values_on_each_test_and_each_call.push(values_on_each_call);

                                        if synth_fun.get_type(&name_of_non_terminal).unwrap() != synth_fun.get_return_type() {
                                            // 注意，对于返回值类型不匹配的程序，没有必要再计算是否满足约束，但之前的等价性检查仍然是可以进行的
                                            pass_test = false;
                                        }
                                        else {
                                            // 只对返回值类型匹配的程序进行约束检查即可
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
                                                        break '_enum_test;
                                                    },
                                                    Err(e) => panic!("{:?}", e)
                                                };
                                                if !res_value.is_pass() {
                                                    trace!(
                                                        "程序 {:?} 未通过测试 {:?} 的约束 {:?}",
                                                        exp,
                                                        test,
                                                        constaint.get_body()
                                                    );
                                                    pass_test = false;
                                                }
                                            }
                                        }

                                    }
                                    // 如果测试通过，就写在 program_passes_tests_ref 中
                                    if pass_test {
                                        info!(
                                            "程序 {:?} 通过所有测试",
                                            exp
                                        );
                                        let _ = program_passes_tests_ref.set(exp);  // 注意，假如其他线程已经找到解，这里的 set 可能会被忽略，这正是我们预期的行为
                                        sub_and_wake_when_zero(processing_task_ref, turn_is_finish_ref);
                                        turn_is_finish_ref.fetch_add(1, ATOMIC_WRITE_ORDER);
                                        atomic_wait::wake_all(turn_is_finish_ref as *const AtomicU32);
                                        break;
                                    }
                                    // 否则，检查当前的 f 是否需要被等价性消减
                                    if valid_program {
                                        prev_results_ref.read(
                                            &name_of_non_terminal, 
                                            |_, v| match v.insert(values_on_each_test_and_each_call) {
                                                Ok(_) => {
                                                    // 如果插入成功，说明结果没有出现过
                                                    // 将 exp 写入可用表达式组之中
                                                    match available_exps_ref.read(
                                                        &name_of_non_terminal, 
                                                        |_, v| {
                                                            v.push(exp);
                                                            // 对于合法的程序，只有写入完成后才视作该任务结束
                                                            sub_and_wake_when_zero(processing_task_ref, turn_is_finish_ref);
                                                        }
                                                    ) {
                                                        Some(_) => (),
                                                        None => {
                                                            println!("{:?}", available_exps_ref);
                                                            println!("{:?}", processing_task_ref);
                                                            panic!("插入失败");
                                                        }
                                                    }
                                                    
                                                    // 这里假定所有非终结符对应的 hashmap 已经被主线程创建
                                                },
                                                // 如果插入失败，说明结果出现过，不用写入
                                                Err(_) => {
                                                    debug!("表达式：{:?} 已经出现过", exp);
                                                    sub_and_wake_when_zero(processing_task_ref, turn_is_finish_ref);
                                                }
                                            }
                                        ).unwrap();  // 这里假定所有非终结符对应的 hashmap 已经被主线程创建
                                    }
                                    else {
                                        sub_and_wake_when_zero(processing_task_ref, turn_is_finish_ref);
                                    }
                                    // if processing_task_ref.clone().fetch_sub(1, ATOMIC_ORDER) == 1 {
                                    //     // 如果当前任务是最后一个任务，说明所有任务已经完成
                                    //     turn_is_finish_ref.fetch_add(1, ATOMIC_ORDER);
                                    //     atomic_wait::wake_all(turn_is_finish_ref.borrow() as *const AtomicU32);
                                    //     info!("本轮所有任务完成")
                                    // }
                                }
                                debug!("线程退出");
                            }
                        ))
                    }

                    // 主线程负责生成新的 exp，以及找到通过所有测试的程序时发给 smt solver
                    'enum_size: while program_passes_tests.get().is_none() {
                        // 还没有找到解时

                        // 依次枚举程序大小
                        // 该层程序中，可以留待未来使用的
                        // 这两个变量只由主线程使用
                        let mut candidate_exprs: AllCandidateExprs<Identifier, Values> = HashMap::new();
                        let mut prog_size = 1;
                        let available_exps_ref = available_exps_ref.clone();
                        candidate_exprs.insert(prog_size, ConcurrentHashMap::new());
                        let all_rules = synth_fun.get_all_rules_with_non_terminals();
                        let all_non_terminals = all_rules.keys().cloned().collect::<HashSet<_>>();
                        for non_terminal in &all_non_terminals {
                        // 初始化一些信息
                            prev_results.insert((*non_terminal).clone(), ConcurrentHashSet::new()).unwrap();
                        }
                        loop {
                            info!("枚举程序大小：{}", prog_size);
                            // 重置状态
                            turn_is_finish_ref.store(0, ATOMIC_WRITE_ORDER);
                            // let _ = all_tasks_done_flag.take();
                            // 我们假设所有线程处理程序大小是同步的，主线程会等待当前大小程序全部处理完，再处理下一个大小的程序
                            {
                                let mut available_exps_ref = available_exps_ref.write().unwrap();
                                for non_terminal in &all_non_terminals {
                                // 初始化一些信息
                                    available_exps_ref.insert((*non_terminal).clone(), ExpQueue::default()).unwrap();   // 注意由于每轮结束时，available_exps 会被清空，因此这里需要重建
                                    prev_results.get(non_terminal).unwrap().clear();
                                }
                            }

                            let tx = tx_rc_ref_cell.clone();
                            // tx.borrow_mut().send(Message::Exp(synth_fun.get_name().clone(), 
                            //     Exp::Apply(
                            //         Identifier::from_name("*".to_string()), 
                            //         vec![
                            //             Exp::Apply(
                            //                 Identifier::from_name("+".to_string()),
                            //                 vec![
                            //                     Exp::Value(base::language::Terms::Var(Identifier::from_name("x".to_string()))),
                            //                     Exp::Value(base::language::Terms::Var(Identifier::from_name("x".to_string()))),
                            //                 ]
                            //             ),
                            //             Exp::Apply(
                            //                 Identifier::from_name("-".to_string()),
                            //                 vec![
                            //                     Exp::Value(base::language::Terms::Var(Identifier::from_name("y".to_string()))),
                            //                     Exp::Value(base::language::Terms::Var(Identifier::from_name("z".to_string()))),
                            //                 ]
                            //             ),
                            //         ]
                            //     )
                            // )).unwrap();
                            // println!("candidate_exprs: {:?}", candidate_exprs);
                            // 枚举所有的规则
                            processing_task_ref.fetch_add(100, ATOMIC_WRITE_ORDER); // 防止在枚举过程中归零
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
                                            processing_task_ref.fetch_add(1, ATOMIC_WRITE_ORDER);

                                            tx.send(Message::Exp(non_terminal.clone(), res_exp)).unwrap();
                                            return true;
                                        }
                                    );
                                    info!("枚举完成: {:?}", rule.get_body());
                                }
                            }
                            processing_task_ref.fetch_sub(100, ATOMIC_WRITE_ORDER);
                            if processing_task_ref.load(ATOMIC_READ_ORDER) != 0 {
                                info!("当前任务数量：{}", processing_task_ref.load(ATOMIC_READ_ORDER));
                                // 先检查一下是否有任务
                                // 无论是任务已经完成还是本层没有任务，判断一下都是正确的
                                while turn_is_finish_ref.load(ATOMIC_READ_ORDER) == 0 {
                                    atomic_wait::wait(turn_is_finish_ref, 0);
                                    if true {
                                        if  processing_task_ref.load(ATOMIC_READ_ORDER) != 0 && program_passes_tests_ref.get().is_none() {
                                            panic!("任务没有完成");
                                        }
                                    }
                                }
                                // atomic_wait::wait(turn_is_finish_ref, 0);
                                // if !cfg!(debug_assertions) {
                                //     if  processing_task_ref.load(ATOMIC_READ_ORDER) != 0 {
                                //         panic!("任务没有完成");
                                //     }
                                // }
                            }
                            info!("本轮所有任务完成，主线程被唤醒");
                            // 如果找到通过测试的解
                            if let Some(exp) = program_passes_tests_ref.get() {
                                // let mut solver = z3_solver_generator();
                                let now_prog = synth_fun.exp_to_basic_fun(Some(scope_arc_ref.clone()), &exp);
                                let res = z3_solver_call(&now_prog);
                                clean_up_sub_threads(MAX_THREADS, &mut tx.borrow_mut(), &thread_exit_lock);
                                match res {
                                    Ok(either_val) => match either_val {
                                        Left(v) => {
                                            debug!("找到新反例：{:?}", v);
                                            counter_examples.push(v);
                                            break 'enum_size;   // 如果找到了反例，直接退出枚举 size 的循环
                                        }
                                        Right(e) => {
                                            println!("The exp satisifies all constraints: {:?}", e);
                                            info!("找到解：{:?}", e);
                                            return Ok(exp.clone());
                                        }
                                    },
                                    Err(e) => {
                                        panic!("Error: {:?}", e);
                                    }
                                }
                            }
                            info!("没有找到解，进入下一层");
                            // 否则，将本层得到的表达式加入可用表达式，进入下一层
                            // 将本层得到的表达式加入可用表达式
                            {
                                let _wait_sub_threads_complete = thread_exit_lock.write().unwrap();
                                info!("所有子线程停止运行");
                                let mut available_exps_ref = available_exps_ref.write().unwrap();
                                let mut temp_available_exps: ConcurrentHashMap<Identifier, ExpQueue::<Identifier, Values>> = ConcurrentHashMap::new();
                                swap(&mut temp_available_exps, &mut available_exps_ref);
                                candidate_exprs.insert(prog_size, temp_available_exps);
                            }
                            // println!("candidate_exprs: {:?}", candidate_exprs);
                            prog_size += 1;
                            // if prog_size > 6 {
                            //     panic!()
                            // }
                        }
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