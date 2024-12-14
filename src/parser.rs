pub mod parser{

    use std::cell::OnceCell;

    use crate::base::{function::{PositionedExecutable, VarIndex}, language::{DefineFun, Exp, Terms, Type}, logic::{parse_logic_tag, LogicTag}, scope::{Scope, ScopeImpl}};

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

    fn parse_logic(input: &sexp::Sexp) -> Result<LogicTag, String> {
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

    use crate::base::{function::{BuiltinFunction, ExecError, PositionedExecutable, VarIndex}, language::{DefineFun as BaseDefineFun, Type}, logic::LogicTag};
    use super::parser::{AtomParser, ContextFreeSexpParser, ContextSexpParser, MutContextSexpParser};
    use crate::base::logic::{Logic, parse_logic_tag};
    use crate::base::scope::{Scope, ScopeImpl};
    pub type Context<'a, Identifier, Values, Types> = ScopeImpl<Identifier, Types, Values, RcFunctionVar<'a, Identifier, Values>>;
    pub enum Command<
        'a,
        Identifier: VarIndex + Clone + Eq + Hash + Debug,
        PrimValues: Copy + Eq,
        Types: Copy
    > {
        SetLogic(LogicTag),
        DefineFun(Arc<DefineFun<'a, Identifier, PrimValues, Types>>)
        // TODO
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
          Types: ContextFreeSexpParser + Copy + Type + 'static
    {
        fn head() -> sexp::Atom {
            sexp::Atom::S(" ".to_string())
        }
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
                                // TODO: Other commands
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