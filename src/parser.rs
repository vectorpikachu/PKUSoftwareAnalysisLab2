pub mod parser{

    use crate::base::{function::{PositionedExecutable, VarIndex}, language::{DefineFun, Exp, Terms}, scope::{Scope, ScopeImpl}};

    trait AtomParser 
    where Self: Sized
    {
        fn parse(input: &sexp::Atom) -> Result<Self, String>;
    }
    trait ContextFreeSexpParser
    where Self: Sized
    {
        fn parse(input: &sexp::Sexp) -> Result<Self, String>;
    }

    impl <T: AtomParser> ContextFreeSexpParser for T {
        fn parse(input: &sexp::Sexp) -> Result<Self, String> {
            match input {
                sexp::Sexp::Atom(atom) => Self::parse(atom),
                _ => Err("Expected an atom".to_string())
            }
        }
    }

    trait ContextSexpParser<Identifier, Values, FunctionVar, Types, Context>
    where Self: Sized,
          Identifier: Sized + AtomParser,
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

    fn parse_exp<Identifier: Sized + AtomParser + Clone, Values: Sized + AtomParser + Copy>(
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

    impl<
        Identifier: Sized + AtomParser + VarIndex,
        Values: Sized + AtomParser + Copy,
        FunctionVar: PositionedExecutable<Identifier, Values, Values>,
        Types: ContextFreeSexpParser,
        Context: Scope<Identifier, Types, Values, FunctionVar>
    > ContextSexpParser<Identifier, Values, FunctionVar, Types, Context> for DefineFun<Identifier, Values, Types, FunctionVar> {
        fn head() -> sexp::Atom {
            sexp::Atom::S("define-fun".to_string())
        }
        fn parse(input: &sexp::Sexp, context: &mut Context) -> Result<Self, String> {
            let inputs = match input {
                sexp::Sexp::List(inputs) => inputs,
                _ => return Err(format!("Expected a list in{:?}, got {:?}", Self::head(), input))
            };
            if inputs.len() != 5 {
                return Err(format!("Expected 5 arguments in {:?}, got {:?}", Self::head(), inputs.len()));
            }
            let id = match inputs[1] {
                sexp::Sexp::Atom(ref atom) => match Identifier::parse(atom) {
                    Ok(id) => id,
                    Err(e) => return Err(e)
                },
                _ => return Err("Expected an atom in the second position of define-fun".to_string())
            };
            let args = match inputs[2] {
                sexp::Sexp::List(list) => {
                    let mut paras = Vec::new();
                    for item in list {
                        let (arg_name, arg_type) = parse_two_pair(paras);
                        let arg_name: Identifier = ContextFreeSexpParser::parse(&arg_name)?;
                        let arg_type: Types = ContextFreeSexpParser::parse(&arg_type)?;
                        paras.push((arg_name, arg_type));
                    }
                    paras
                }
                _ => return Err("Expected a list in the third position of define-fun".to_string())
            };
            let return_type: Types = ContextFreeSexpParser::parse(&inputs[4])?; 
            let body = parse_exp(&inputs[3])?;
            let contexts = context.
            Ok(
                DefineFun {
                    name: id.to_name(),
                    var_index: id,
                    args,
                    context,
                    return_type,
                    body

                }
            )
        }

    }
}