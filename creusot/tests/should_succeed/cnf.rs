extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

use creusot_contracts::derive::Clone;

use std::cmp;

#[derive(Clone)]
struct Valuation(Vec<bool>);

enum Formula {
    Atom(usize),
    Not(Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    And(Box<Formula>, Box<Formula>),
}

impl Formula {
    #[ensures(self.atoms_in_range(@result + 1))]
    fn max_atom(&self) -> usize {
        match self {
            Formula::Atom(a) => *a,
            Formula::Not(f) => f.max_atom(),
            Formula::Or(f1, f2) => cmp::max(f1.max_atom(), f2.max_atom()),
            Formula::And(f1, f2) => cmp::max(f1.max_atom(), f2.max_atom()),
        }
    }

    #[predicate]
    fn atoms_in_range(self, n: Int) -> bool {
        pearlite! {
            match self {
                Formula::Atom(a) => @a < n,
                Formula::Not(f) => f.atoms_in_range(n),
                Formula::Or(f1, f2) => f1.atoms_in_range(n) && f2.atoms_in_range(n),
                Formula::And(f1, f2) => f1.atoms_in_range(n) && f2.atoms_in_range(n),
            }
        }
    }

    #[predicate]
    #[requires(self.atoms_in_range((@val.0).len()))]
    fn eval(self, val: Valuation) -> bool {
        match self {
            Formula::Atom(a) => (val.0)[a],
            Formula::Not(f) => !f.eval(val),
            Formula::Or(f1, f2) => f1.eval(val) || f2.eval(val),
            Formula::And(f1, f2) => f1.eval(val) && f2.eval(val),
        }
    }
}

#[derive(Clone, Copy)]
enum Pol {
    Pos,
    Neg,
}

#[derive(Clone, Copy)]
struct Lit {
    atom: usize,
    polarity: Pol,
}

impl Lit {
    #[ensures(forall<v: Valuation> @atom < (@v.0).len() ==> (result.eval(v) == (v.0)[atom]))]
    fn pos(atom: usize) -> Self {
        Self {
            atom,
            polarity: Pol::Pos,
        }
    }

    #[ensures(forall<v: Valuation> self.atoms_in_range((@v.0).len()) ==> result.atoms_in_range((@v.0).len()))]
    #[ensures(forall<v: Valuation> self.atoms_in_range((@v.0).len()) ==> (result.eval(v) == !self.eval(v)))]
    fn inv(self) -> Self {
        match self.polarity {
            Pol::Pos => Self {
                polarity: Pol::Neg,
                ..self
            },
            Pol::Neg => Self {
                polarity: Pol::Pos,
                ..self
            },
        }
    }

    #[predicate]
    fn atoms_in_range(self, n: Int) -> bool {
        pearlite! {
            @self.atom < n
        }
    }

    #[predicate]
    #[requires(self.atoms_in_range((@val.0).len()))]
    fn eval(self, val: Valuation) -> bool {
        match self.polarity {
            Pol::Pos => (val.0)[self.atom],
            Pol::Neg => !(val.0)[self.atom],
        }
    }
}

struct Clause {
    literals: Vec<Lit>, // [Option<Pol>; N]
}

impl Clause {
    fn new1(lit: Lit) -> Self {
        let mut literals = Vec::new();
        literals.push(lit);

        Clause {
            literals,
        }
    }

    fn new2(lits: (Lit, Lit)) -> Self {
        let mut literals = Vec::new();
        literals.push(lits.0);
        literals.push(lits.1);

        Clause {
            literals,
        }
    }

    fn new3(lits: (Lit, Lit, Lit)) -> Self {
        let mut literals = Vec::new();
        literals.push(lits.0);
        literals.push(lits.1);
        literals.push(lits.2);
        
        Clause {
            literals,
        }
    }

    #[predicate]
    fn atoms_in_range(self, n: Int) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self.literals).len() ==>
                (@self.literals)[i].atoms_in_range(n)
        }
    }

    #[predicate]
    #[requires(self.atoms_in_range((@val.0).len()))]
    fn eval(self, val: Valuation) -> bool {
        pearlite! {
            exists<i: Int> 0 <= i && i < (@self.literals).len() &&
                (@self.literals)[i].eval(val)
        }
    }
}

struct Cnf {
    clauses: Vec<Clause>,
    current_atom_idx: usize,
}

impl Cnf {
    //#[ensures((exists<v: Valuation> f.eval(&v)) == (exists<v: Valuation> result.eval(&v)))]
    fn new(f: &Formula) -> Self {
        let mut ctx = Self {
            clauses: Vec::new(),
            current_atom_idx: f.max_atom() + 1,
        };
        proof_assert!(ctx.invariant());
        let x = ctx.push_formula(f);
        ctx.clauses.push(Clause::new1(x));
        ctx
    }

    #[requires(self.invariant())]
    #[ensures((^self).invariant())]
    fn push_or(&mut self, b: Lit, c: Lit) -> Lit {
        // == push_and(b.inv(), c.inv()).inv()
        let a = self.next_var();
        self.clauses.push(Clause::new3((a.inv(), b, c)));
        self.clauses.push(Clause::new2((a, b.inv())));
        self.clauses.push(Clause::new2((a, c.inv())));
        a
    }

    #[requires(self.invariant())]
    #[ensures((^self).invariant())]
    fn push_and(&mut self, b: Lit, c: Lit) -> Lit {
        let a = self.next_var();
        self.clauses.push(Clause::new3((a, b.inv(), c.inv())));
        self.clauses.push(Clause::new2((a.inv(), b)));
        self.clauses.push(Clause::new2((a.inv(), c)));
        a
    }

    #[requires(self.invariant())]
    #[ensures((^self).invariant())]
    fn next_var(&mut self) -> Lit {
        let v = self.current_atom_idx;
        self.current_atom_idx += 1;
        Lit::pos(v)
    }

    #[requires(self.invariant())]
    #[ensures((^self).invariant())]
    fn push_formula(&mut self, f: &Formula) -> Lit {
        match f {
            Formula::Atom(a) => Lit::pos(*a),
            Formula::Not(f1) => self.push_formula(f1).inv(),
            Formula::Or(f1, f2) => {
                let f1_idx = self.push_formula(f1);
                let f2_idx = self.push_formula(f2);
                self.push_or(f1_idx, f2_idx)
            }
            Formula::And(f1, f2) => {
                let f1_idx = self.push_formula(f1);
                let f2_idx = self.push_formula(f2);
                self.push_and(f1_idx, f2_idx)
            }
        }
    }

    #[predicate]
    fn invariant(self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                (@self.clauses)[i].atoms_in_range(@self.current_atom_idx)
        }
    }

    #[predicate]
    #[requires(self.invariant())]
    #[requires(@self.current_atom_idx == (@val.0).len())]
    fn eval(self, val: Valuation) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self.clauses).len() ==>
                (@self.clauses)[i].eval(val)
        }
    }
}
