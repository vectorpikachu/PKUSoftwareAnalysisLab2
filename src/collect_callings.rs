pub mod collect_callings {
    use std::{collections::HashMap, hash::Hash};

    use crate::base;
    use crate::base::language::{Constraint, Exp, Terms};

    extern crate rand;

    use rand::Rng;
    use rand::distributions::Alphanumeric;
    use rand::thread_rng; 

    /// 生成一个随机字符串作为标识符
    // fn gen_identifier <
    //     Identifier: Clone + Hash + Eq,
    // > () -> Identifier {
        // let mut rng = thread_rng();
        // let identifier: String = std::iter::repeat(())
        //     .map(|()| rng.sample(Alphanumeric))
        //     .map(char::from)
        //     .take(8) // 生成8个字符的随机字符串
        //     .collect(); // 收集到字符串中
        // identifier
    // }

    fn trans_calling<
        Identifier: Clone + Hash + Eq,
        Values: Copy + Eq
    > (
        exp: &Exp<Identifier, Values>,
        fun_to_synth: &Identifier,
        callings: &mut Vec<(Identifier, Exp<Identifier, Values>)>,
    ) -> Exp<Identifier, Values> {
        match exp {
            Exp::Value(value) => {
                Exp::Value(value.clone())
            }
            Exp::Apply(fun, args) => {
                let mut new_args = args
                   .into_iter()
                   .map(|x: &Exp<Identifier, Values>| trans_calling(x, fun_to_synth, callings))
                   .collect();
                
                if fun == fun_to_synth{

                    //ToDo 如何生成唯一的标识符
                    // let calling_id = gen_identifier();
                    let calling_id = fun.clone();
                    callings.push((calling_id.clone(), exp.clone()));
                    Exp::Value(Terms::Var(calling_id.clone()))
                }
                else {
                    Exp::Apply(fun.clone(), new_args)
                }
            }
        }
    }

    pub fn collect_callings_of_fun<
        Identifier: Clone + Hash + Eq,
        Values: Copy + Eq
    > (
        fun_to_synth: &Identifier,
        constraints: &Vec<Constraint<Identifier, Values>>,
    ) -> (Vec<Constraint<Identifier, Values>>, Vec<(Identifier, Exp<Identifier, Values>)>) {
        let mut callings = Vec::new();
        let mut new_constraints = Vec::new();

        for constraint in constraints {
            new_constraints.push( Constraint::new(trans_calling(&constraint.get_body(), fun_to_synth, &mut callings)));
        }

        (new_constraints, callings)
    }
}