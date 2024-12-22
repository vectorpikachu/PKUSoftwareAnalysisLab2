pub mod collect_callings {
    use std::{collections::HashMap, hash::Hash};

    use crate::base::language::{Constraint, Exp};

pub fn collect_callings_of_fun<
        Identifier: Clone + Hash + Eq,
        Values: Copy + Eq
    > (
        fun_to_synth: &Identifier,
        constraints: &Vec<Constraint<Identifier, Values>>,
    ) -> (Vec<Constraint<Identifier, Values>>, HashMap<Identifier, Exp<Identifier, Values>>) {
        let mut callings = HashMap::new();
        let mut new_constraints = Vec::new();
        (new_constraints, callings)
    }
}