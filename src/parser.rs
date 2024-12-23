pub mod parser{

    use std::{cell::OnceCell, collections::{HashMap, HashSet}};

    use crate::base::{function::{PositionedExecutable, VarIndex}, language::{Constraint, DeclareVar, DefineFun, Exp, Rule, SynthFun, Terms, Type}, logic::{parse_logic_tag, LogicTag}, scope::{Scope, ScopeImpl}};

    pub trait AtomParser 
    where Self: Sized
    {
        fn parse(input: &sexp::Atom) -> Result<Self, String>;
    }

    impl AtomParser for String {
        fn parse(input: &sexp::Atom) -> Result<Self, String> {
            match input {
                sexp::Atom::S(s) => Ok(s.clone()),
                _ => Err("Expected a string".to_string())
            }
        }
    }
    impl AtomParser for i64 {
        fn parse(input: &sexp::Atom) -> Result<Self, String> {
            match input {
                sexp::Atom::I(i) => Ok(*i),
                _ => Err("Expected an integer".to_string())
            }
        }
    }

    impl <T: Type> AtomParser for T {
        fn parse(input: &sexp::Atom) -> Result<Self, String> {
            match input {
                sexp::Atom::S(s) => match T::from_identifier(s) {
                    Some(t) => Ok(t),
                    None => Err(format!("Unknown type: {}", s))
                },
                _ => Err("Expected a string".to_string())
            }
        }
    }

    pub trait ContextFreeSexpParser
    where Self: Sized
    {
        fn parse(input: &sexp::Sexp) -> Result<Self, String>;
    }

    impl <T: AtomParser> ContextFreeSexpParser for T {
        fn parse(input: &sexp::Sexp) -> Result<Self, String> {
            match input {
                sexp::Sexp::Atom(atom) => Self::parse(atom),
                _ => Err(format!("Expected an atom, got {:?}", input))
            }
        }
    }

    pub trait ContextSexpParser<Identifier, Values, FunctionVar, Types, Context>
    where Self: Sized,
          Identifier: Sized + AtomParser + Clone,
          Values: Sized + AtomParser + Copy,
          FunctionVar: PositionedExecutable<Identifier, Values, Values>,
          Types: ContextFreeSexpParser,
          Context: Scope<Identifier, Types, Values, FunctionVar>
    {
        fn head() -> sexp::Atom;
        fn parse(input: &sexp::Sexp, context: &Context) -> Result<Self, String>;
    }
    pub trait MutContextSexpParser<Identifier, Values, FunctionVar, Types, Context>
    where Self: Sized,
          Identifier: Sized + AtomParser + Clone,
          Values: Sized + AtomParser + Copy,
          FunctionVar: PositionedExecutable<Identifier, Values, Values>,
          Types: ContextFreeSexpParser,
          Context: Scope<Identifier, Types, Values, FunctionVar>
    {
        fn head() -> sexp::Atom;
        fn parse(input: &sexp::Sexp, context: &mut Context) -> Result<Self, String>;
    }


    fn parse_two_pair(input: &sexp::Sexp) -> (sexp::Sexp, sexp::Sexp) {
        match input {
            sexp::Sexp::List(list) => {
                if list.len() != 2 {
                    panic!("Expected a list of length 2, got {:?}", list.len());
                }
                (list[0].clone(), list[1].clone())
            }
            _ => panic!("Expected a list, got {:?}", input)
        }
    }

    pub fn parse_logic(input: &sexp::Sexp) -> Result<LogicTag, String> {
        match parse_two_pair(input) {
            (sexp::Sexp::Atom(atom), sexp::Sexp::Atom(tag)) => {
                if atom == sexp::Atom::S("set-logic".to_string()) {
                    Ok(parse_logic_tag(tag))
                } else {
                    Err("Expected set-logic".to_string())
                }
            }
            _ => Err("Expected a list of length 2".to_string())
        }
    }

    fn parse_three_pair(input: &sexp::Sexp) -> (sexp::Sexp, sexp::Sexp, sexp::Sexp) {
        match input {
            sexp::Sexp::List(list) => {
                if list.len() != 3 {
                    panic!("Expected a list of length 3, got {:?}", list.len());
                }
                (list[0].clone(), list[1].clone(), list[2].clone())
            }
            _ => panic!("Expected a list, got {:?}", input)
        }
    }

    // impl<
    //     Identifier: Sized + AtomParser,
    //     Values: Sized + AtomParser + Copy,
    //     FunctionVar: PositionedExecutable<Identifier, Values, Values>,
    //     Types,
    //     Context: Scope<Identifier, Types, Values, FunctionVar>
    // > SexpParser<Identifier, Values, FunctionVar, Types, Context> for Exp<Identifier, Values> {
    //     fn head() -> sexp::Atom {
    //         sexp::Atom::S("exp".to_string())
    //     }
    // }

    fn parse_exp<Identifier: Sized + AtomParser + Clone + Eq, Values: Sized + AtomParser + Copy + Eq>(
        input: &sexp::Sexp
    ) -> Result<Exp<Identifier, Values>, String> {
        match input {
            sexp::Sexp::Atom(atom) => {
                match Identifier::parse(atom) {
                    Ok(id) => Ok(Exp::Value(Terms::Var(id))),
                    Err(e) => match Values::parse(atom) {
                        Ok(v) => Ok(Exp::Value(Terms::PrimValue(v))),
                        Err(e) => Err(e)
                    }
                }
            }
            sexp::Sexp::List(list) => {
                let mut exps = Vec::new();
                if list.len() == 1 {
                    return parse_exp::<Identifier, Values>(&list[0]);
                }
                let mut it = list.iter();
                let first = it.next().unwrap();
                for item in it {
                    exps.push(parse_exp::<Identifier, Values>(item)?);
                }
                let id_first = match parse_exp::<Identifier, Values>(first) {
                    Ok(Exp::Value(Terms::Var(id))) => id,
                    _ => return Err("Expected a variable in the first position of an application".to_string())
                };
                Ok(Exp::Apply(id_first, exps))
            }
        }
    }
    /// 注意这里我们实现上其实有点小问题，直接引用了 context。
    /// 换言之，declare-fun 的结果将随着 context 的变动而变动
    /// （比如如果按顺序 parse，那么 declare-fun 的结果将是顺序无关的，按照当前的语义我们可以写出互递归的函数）
    impl<
        'a,
        Identifier: Sized + AtomParser + VarIndex + Eq,
        Values: Sized + AtomParser + Copy + Eq,
        FunctionVar: PositionedExecutable<Identifier, Values, Values>,
        Types: ContextFreeSexpParser + Type + Copy,
        Context: Scope<Identifier, Types, Values, FunctionVar>
    > ContextFreeSexpParser for DefineFun<Identifier, Values, Types, FunctionVar, Context> {
        fn parse(input: &sexp::Sexp) -> Result<Self, String> {
            let inputs = match input {
                sexp::Sexp::List(inputs) => inputs,
                _ => return Err(format!("Expected a list in parse declare-fun, got {:?}", input))
            };
            if inputs.len() != 5 {
                return Err(format!("Expected 5 arguments in parse declare-fun, got {:?}", inputs.len()));
            }
            let id = match inputs[1] {
                sexp::Sexp::Atom(ref atom) => match Identifier::parse(atom) {
                    Ok(id) => id,
                    Err(e) => return Err(e)
                },
                _ => return Err("Expected an atom in the second position of define-fun".to_string())
            };
            let args = match inputs[2] {
                sexp::Sexp::List(ref list) => {
                    let mut paras = Vec::new();
                    for item in list {
                        let (arg_name, arg_type) = parse_two_pair(&item);
                        let arg_name: Identifier = ContextFreeSexpParser::parse(&arg_name)?;
                        let arg_type: Types = ContextFreeSexpParser::parse(&arg_type)?;
                        paras.push((arg_name, arg_type));
                    }
                    paras
                }
                _ => return Err("Expected a list in the third position of define-fun".to_string())
            };
            let return_type: Types = ContextFreeSexpParser::parse(&inputs[3])?; 
            let body = parse_exp(&inputs[4])?;
            Ok(
                DefineFun {
                    var_index: id,
                    args,
                    context: OnceCell::new(),
                    return_type,
                    body,
                    _phantom: std::marker::PhantomData
                }
            )
        }
    }
    use std::hash::Hash;
    use std::fmt::Debug;
    fn parse_rules<
        Identifier: Debug + AtomParser + VarIndex + Eq + Hash,
        Types: ContextFreeSexpParser + Type + Copy,
        Values: Sized + AtomParser + Copy + Eq + Debug,
    >(input: &sexp::Sexp) -> Result<(Identifier, Types, Vec<Rule<Identifier, Values>>), String> {
        match input {
            sexp::Sexp::List(list) => {
                if list.len() != 3 {
                    return Err(format!("Expected a list of length 3, got {:?}", list.len()));
                }
                let id = ContextFreeSexpParser::parse(&list[0])?;
                let ty = ContextFreeSexpParser::parse(&list[1])?;
                let body = &list[2];
                if let sexp::Sexp::List(ref body_list) = body {
                    let mut rules = Vec::new();
                    for item in body_list {
                        rules.push(
                            Rule::new(
                                parse_exp(item)?
                            )
                        )
                    }
                    Ok((id, ty, rules))
                } else {
                    Err("Expected a list in the third position of a rule".to_string())
                }
            }
            _ => Err("Expected a list".to_string())
        }
    }

    impl<
        Identifier: Sized + AtomParser + VarIndex + Eq + Hash + Debug,
        Values: Sized + AtomParser + Copy + Eq + Debug,
        Types: ContextFreeSexpParser + Type + Copy,
    > ContextFreeSexpParser for SynthFun<Identifier, Values, Types> {
        fn parse(input: &sexp::Sexp) -> Result<Self, String> {
            let input = match input {
                sexp::Sexp::List(inputs) => inputs,
                _ => return Err(format!("Expected a list in parse synth-fun, got {:?}", input))
            };
            if input.len() != 5 {
                return Err(format!("Expected 5 arguments in parse synth-fun, got {:?}", input.len()));
            }
            let id: Identifier = ContextFreeSexpParser::parse(&input[1])?;
            let args = match &input[2] {
                sexp::Sexp::List(ref list) => {
                    let mut paras = Vec::new();
                    for item in list {
                        let (arg_name, arg_type) = parse_two_pair(&item);
                        let arg_name: Identifier = ContextFreeSexpParser::parse(&arg_name)?;
                        let arg_type: Types = ContextFreeSexpParser::parse(&arg_type)?;
                        paras.push((arg_name, arg_type));
                    }
                    paras
                }
                _ => return Err("Expected a list in the third position of synth-fun".to_string())
            };
            let return_type: Types = ContextFreeSexpParser::parse(&input[3])?;
            let mut id_to_type: HashMap<Identifier, Types> = HashMap::new();
            let mut non_termianal_to_rules: HashMap<Identifier, Vec<Rule<Identifier, Values>>> = HashMap::new();
            let mut non_terminals: HashSet<Identifier> = HashSet::new();
            if let sexp::Sexp::List(ref body) = input[4] {
                for non_terminal_rule in body {
                    let (id, ty, rules) = parse_rules::<Identifier, Types, _>(non_terminal_rule)?;
                    id_to_type.insert(id.clone(), ty);
                    non_termianal_to_rules.insert(id.clone(), rules);
                    non_terminals.insert(id);
                }
            } else {
                return Err("Expected a list in the fourth position of synth-fun".to_string());
            }
            // for (_, rules) in non_termianal_to_rules.iter_mut() {
            //     for rule in rules {
            //         rule.counts_init(
            //             |id| non_terminals.get(id).is_some()
            //         );
            //     }
            // }
            Ok(
                SynthFun::new(
                    id,
                    args,
                    return_type,
                    non_termianal_to_rules,
                    id_to_type,
                )
            )
        }
    }

    impl<
        Identifier: Sized + AtomParser + VarIndex + Eq + Hash + Debug,
        Types: ContextFreeSexpParser + Type + Copy,
    > ContextFreeSexpParser for DeclareVar<Identifier, Types> {
        fn parse(input: &sexp::Sexp) -> Result<Self, String> {
            let input = match input {
                sexp::Sexp::List(inputs) => inputs,
                _ => return Err(format!("Expected a list in parse declare-var, got {:?}", input))
            };
            if input.len() != 3 {
                return Err(format!("Expected 3 arguments in parse declare-var, got {:?}", input.len()));
            }
            let id: Identifier = ContextFreeSexpParser::parse(&input[1])?;
            let ty: Types = ContextFreeSexpParser::parse(&input[2])?;
            Ok(DeclareVar::new(id, ty))
        }
    }

    impl<
        Identifier: AtomParser + Clone + Eq,
        Types: AtomParser + Copy + Eq,
    > ContextFreeSexpParser for Constraint<Identifier, Types>{
        fn parse(input: &sexp::Sexp) -> Result<Self, String> {
            let input = match input{
                sexp::Sexp::List(inputs) => inputs,
                _ => return Err(format!("Expected a list in parse constraint, got {:?}", input))
            };
            if input.len() != 2 {
                return Err(format!("Expected 2 arguments in parse constraint, got {:?}", input.len()));
            }
            let body = parse_exp(&input[1])?;
            Ok(Constraint::new(body))
        }
    }

}

/// 使用 RcFunctionVar 实现总体 FunctionVar 的上下文
pub mod rc_function_var_context {
    use std::{fmt::{Debug, DebugList}, hash::Hash, sync::Arc};

    #[derive(Clone)]
    pub struct RcFunctionVar<'a, Identifier, PrimValues> (
        pub Arc<dyn PositionedExecutable<Identifier, PrimValues, PrimValues> + 'a>,
    );
    
    impl <'a, Identifier: Clone, PrimValues: Copy> PositionedExecutable<Identifier, PrimValues, PrimValues> for RcFunctionVar<'a, Identifier, PrimValues> {
        fn execute (
            &self, 
            args: &Vec<PrimValues>
        ) -> Result<PrimValues, ExecError> {
            self.0.execute(args)
        }
    }

    impl<'a,
        Identifier: VarIndex + Clone + Eq + Hash + Debug + 'a,
        PrimValues: Copy + Debug + Eq + 'a,
        Types: 'a,
        Context: Scope<Identifier, Types, PrimValues, RcFunctionVar<'a, Identifier, PrimValues>> + 'a,
    > FromBasicFun<Identifier, PrimValues, Types, Context> for RcFunctionVar<'a, Identifier, PrimValues>
{
    fn from_basic_fun(
        basic_fun: BasicFun<Identifier, PrimValues, Types, RcFunctionVar<'a, Identifier, PrimValues>, Context>,
    ) -> Self
     {
        RcFunctionVar(Arc::new(basic_fun))
    } 
}

    use crate::base::{function::{BuiltinFunction, ExecError, PositionedExecutable, VarIndex}, language::{BasicFun, Constraint, DeclareVar, DefineFun as BaseDefineFun, FromBasicFun, SynthFun, Type}, logic::LogicTag};
    use super::parser::{AtomParser, ContextFreeSexpParser, ContextSexpParser, MutContextSexpParser};
    use crate::base::logic::{Logic, parse_logic_tag};
    use crate::base::scope::{Scope, ScopeImpl};
    pub type Context<'a, Identifier, Values, Types> = ScopeImpl<Identifier, Types, Values, RcFunctionVar<'a, Identifier, Values>>;
    pub enum Command<
        'a,
        Identifier: VarIndex + Clone + Eq + Hash + Debug,
        PrimValues: Copy + Eq,
        Types: Copy + Eq
    > {
        SetLogic(LogicTag),
        DefineFun(Arc<DefineFun<'a, Identifier, PrimValues, Types>>),
        SynthFun(SynthFun<Identifier, PrimValues, Types>),
        DeclareVar(DeclareVar<Identifier, Types>),
        Constraint(Constraint<Identifier, PrimValues>),
        CheckSynth,
    }  

    type DefineFun<'a, Identifier, Values, Types> = BaseDefineFun<Identifier, Values, Types, RcFunctionVar<'a, Identifier, Values>, Context<'a, Identifier, Values, Types>>;
    impl <'a, 'b, Identifier, Values, Types> MutContextSexpParser <
        Identifier,
        Values,
        RcFunctionVar<'a, Identifier, Values>,
        Types,
        Context<'a, Identifier, Values, Types>
    >
    
    for Command<'a, Identifier, Values, Types>
    where Identifier: AtomParser + VarIndex + Eq + Clone + Hash + Debug + 'static,  // 不想再和生命周期斗争了
          Values: AtomParser + Copy + Debug + Eq + 'static,
          Types: ContextFreeSexpParser + Copy + Type + Eq + 'static
    {
        fn head() -> sexp::Atom {
            sexp::Atom::S(" ".to_string())
        }
        /// 注意该 parser 会在 parse 的同时，完成对应的对上下文的操作。包括为 DefineFun 建立 Arc 的函数指针并加入 context，把 DeclareVar 加入 context
        /// 这样的设计有点耦合，但是懒得改了（：
        fn parse(input: &sexp::Sexp, context: &mut Context<'a, Identifier, Values, Types>) -> Result<Self, String> {
            match input {
                sexp::Sexp::List(list) => {
                    if list.len() == 0 {
                        return Err("Empty command".to_string());
                    }
                    let head = &list[0];
                    if let sexp::Sexp::Atom(atom) = head {
                        if let sexp::Atom::S(s) = atom {
                            match s.as_str() {
                                "define-fun" => {
                                    let declare_fun = DefineFun::<Identifier, Values, Types>::parse(input)?;
                                    let args_type = declare_fun.args.iter().map(|(_, t)| t.clone()).collect();
                                    let var_index = declare_fun.var_index.clone();
                                    let return_type = declare_fun.return_type;
                                    let res_arc = Arc::new(declare_fun);
                                    if let Some(_) = context.add_and_set_function_var(
                                        var_index.clone(),
                                        Types::from_function(args_type, return_type),
                                        RcFunctionVar(res_arc.clone())
                                    )
                                    {
                                        Ok(Command::DefineFun(res_arc.clone()))
                                    }
                                    else {
                                        Err(format!("Variable {} already exists", var_index.to_name()))
                                    }
                                }
                                "synth-fun" => {
                                    let synth_fun = SynthFun::parse(input)?;
                                    Ok(Command::SynthFun(synth_fun))
                                }
                                "declare-var" => {
                                    let declare_var = DeclareVar::<Identifier, Types>::parse(input)?;
                                    context.add_var(declare_var.get_id().clone(), *declare_var.get_type());
                                    Ok(Command::DeclareVar(declare_var))
                                }
                                "constraint" => {
                                    let constraint = Constraint::<Identifier, Values>::parse(input)?;
                                    Ok(Command::Constraint(constraint))
                                }
                                "check-synth" => {
                                    Ok(Command::CheckSynth)
                                }
                                "set-logic" => {
                                    // TODO： 移除这一个分支这是测试用的
                                    let logic = LogicTag::LIA;
                                    Ok(Command::SetLogic(logic))
                                }
                                _ => Err(format!("Unknown command: {}", s))
                            }
                        } else {
                            Err("Expected an string atom".to_string())
                        }
                    } else {
                        Err(format!("Expected an atom, got {:?}", head))
                    }
                }
                _ => Err("Expected a list".to_string())
            }
        }
    }
}