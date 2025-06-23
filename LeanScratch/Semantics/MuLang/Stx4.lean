
/- inductive Ty (rep : Type) : Type -/
/-   | unit -/
/-   | sum  (a b : Ty rep) -/
/-   | prod (a b : Ty rep) -/
/-   | arr  (a b : Ty rep) -/
/-   | fix (functor : rep → Ty rep) -/

/- inductive Stx (trep : _) (srep : Ty trep → Type) : Ty trep → Type -/
/-   | var (v : srep t) : Stx trep srep t -/

/-   | introUnit : Stx trep srep .unit -/

/-   | introProd (a : Stx trep srep aT) (b : Stx trep srep bT) : Stx trep srep (.prod aT bT) -/
/-   | elimProdL (b : Stx trep srep (.prod aT bT)) : Stx trep srep aT -/
/-   | elimProdR (b : Stx trep srep (.prod aT bT)) : Stx trep srep bT -/

/-   | introSumL bT (b : Stx trep srep aT) : Stx trep srep (.sum aT bT) -/
/-   | introSumR aT (b : Stx trep srep bT) : Stx trep srep (.sum aT bT) -/
/-   | elimSum (scrutinee : Stx trep srep (.sum aT bT)) -/
/-       (l : srep aT → Stx trep srep oT) -/
/-       (r : srep bT → Stx trep srep oT) -/
/-       : Stx trep srep oT -/

/-   | introLam (body : srep dom → Stx trep srep out) : Stx trep srep (.arr dom out) -/
/-   | elimLam  (fn : Stx trep srep (.arr dom out)) (arg : Stx trep srep dom) : Stx trep srep out -/

/-   /- | introFix () -/ -/
/-   | elimFix (expr : Stx trep srep (.fix f)) : Stx trep srep f () -/

