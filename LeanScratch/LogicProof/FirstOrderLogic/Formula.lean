import LeanScratch.Vec

namespace FOL

inductive Term {Nm : Type} (Arity : Nm → Nat)
  | const (nm : Nm) (app : Vec (Term Arity) (Arity nm))

inductive Formula {TNm PNm : Type} (TA : TNm → Nat) (PA : PNm → Nat) 
  | pred (nm : PNm) (app : Vec (Term TA) (PA nm)) : Formula TA PA 

  -- We use non-parametric HOAS to get around substitution issues
  | univ : (Term TA → Formula TA PA) → Formula TA PA 
  | exis : (Term TA → Formula TA PA) → Formula TA PA 

  | conj : Formula TA PA → Formula TA PA → Formula TA PA 
  | disj : Formula TA PA → Formula TA PA → Formula TA PA 
  | imp  : Formula TA PA → Formula TA PA → Formula TA PA 
  | iff  : Formula TA PA → Formula TA PA → Formula TA PA 
  | neg  : Formula TA PA → Formula TA PA


inductive DeBrujin.Term {Nm : Type} (Arity : Nm → Nat) (n : Nat)
  | const (nm : Nm) (app : Vec (Term Arity n) (Arity nm))
  | var (v : Fin n)

inductive DeBrujin.Formula {TNm PNm : Type} (TA : TNm → Nat) (PA : PNm → Nat) : Nat → Type
  | pred (nm : PNm) (app : Vec (Term TA n) (PA nm)) : Formula TA PA n

  | univ : Formula TA PA n.succ → Formula TA PA n
  | exis : Formula TA PA n.succ → Formula TA PA n

  | conj : Formula TA PA n → Formula TA PA n → Formula TA PA n
  | disj : Formula TA PA n → Formula TA PA n → Formula TA PA n
  | imp  : Formula TA PA n → Formula TA PA n → Formula TA PA n
  | iff  : Formula TA PA n → Formula TA PA n → Formula TA PA n
  | neg  : Formula TA PA n → Formula TA PA n

def Term.toDeBrujin (t : Term TA) : DeBrujin.Term TA 0 :=
  match t with
  | .const nm args => .const nm (mapper args)
    where
      mapper {k} : Vec (Term TA) k → Vec _ k
        | %[] => %[]
        | hd %:: tl => hd.toDeBrujin %:: mapper tl

namespace DeBrujin

def Term.subst (pt : Fin n.succ) (body : Term TA n.succ) (repl : Term TA n) : Term TA n :=
  match body with
  | .var ⟨x, p⟩ => match h : compare x pt.val with
    | .lt =>
      have xSuccLe := Nat.compare_eq_lt.mp h
      .var ⟨x, by omega⟩
    | .eq => repl
    | .gt =>
      have xSuccLe := Nat.compare_eq_gt.mp h
      .var ⟨x - 1, by omega⟩
  | .const nm args => .const nm (mapper args)
    where
      mapper {k} : Vec (Term TA n.succ) k → Vec (Term TA n) k
        | %[] => %[]
        | hd %:: tl => (hd.subst pt repl) %:: mapper tl

def Term.bvarShift (k : Nat) : Term TA n → Term TA (n + k)
  | .var v => .var $ v.addNat k
  | .const nm args => .const nm (mapper args)
    where
      mapper {m} : Vec (Term TA n) m → Vec (Term TA (n + k)) m
        | %[] => %[]
        | hd %:: tl => (hd.bvarShift k) %:: mapper tl

def Formula.subst
    (pt : Fin n.succ) (body : Formula TA PA n.succ)
    (repl : Term TA n) : Formula TA PA n :=
  match body with
  | .pred nm app => .pred nm (Term.subst.mapper pt repl app)

  | .univ p => .univ $ p.subst pt $ repl.bvarShift 1
  | .exis p => .exis $ p.subst pt $ repl.bvarShift 1

  | .conj a b => .conj (a.subst pt repl) (b.subst pt repl)
  | .disj a b => .disj (a.subst pt repl) (b.subst pt repl)
  | .imp a b => .imp (a.subst pt repl) (b.subst pt repl)
  | .iff a b => .iff (a.subst pt repl) (b.subst pt repl)
  | .neg v => .neg $ v.subst pt repl

theorem substAllEq {m : ℕ} {offset n : ℕ} : offset < offset + m + n + 1 := by
  apply Nat.lt_add_one_of_le
  omega

def Term.substAll (offset : Nat) (int : Term TA (offset + m + n)) : Vec (Term TA (offset + m)) n → Term TA (offset + m)
  | hd %:: tl => (int.subst ⟨offset, substAllEq⟩ (hd.bvarShift _)).substAll offset tl
  | %[] => int

def Formula.substAll (offset : Nat) (inf : Formula TA PA (offset + m + n)) : Vec (Term TA (offset + m)) n → Formula TA PA (offset + m)
  | hd %:: tl => (inf.subst ⟨offset, substAllEq⟩ (hd.bvarShift _)).substAll offset tl
  | %[] => inf

def Term.toHoAS (t : Term TA 0) : FOL.Term TA :=
  match t with
  | .var v => v.elim0
  | .const nm args => .const nm (mapper args)
    where
      mapper {k} : Vec (Term TA 0) k → Vec _ k
        | %[] => %[]
        | hd %:: tl => hd.toHoAS %:: mapper tl

def Formula.sz : Formula TA PA n → Nat
  | .pred _ _ => 1

  | .neg p 
  | .univ p 
  | .exis p => p.sz + 1

  | .conj a b
  | .disj a b
  | .imp a b
  | .iff a b => a.sz + b.sz + 1

theorem Formula.subst.sz
    {repl : Term TA n} {f : Formula TA PA n.succ}
    : (f.subst pt repl).sz = f.sz :=
  match f with
  | .pred _ _ => by simp only [subst]; rfl

  | .neg p
  | .univ p
  | .exis p => by
    simp only [subst]
    change _ + 1 = _ + 1
    rw [Formula.subst.sz]
  | .conj a b
  | .disj a b
  | .imp a b
  | .iff a b => by
    simp only [subst]
    change _ + 1 = _ + 1
    rw [Formula.subst.sz, Formula.subst.sz]

def Formula.toHoAS : Formula TA PA 0 → FOL.Formula TA PA
  | .pred nm app => .pred nm (Term.toHoAS.mapper app)

  | .univ p => .univ fun x => (p.subst ⟨0, Nat.zero_lt_succ _⟩ x.toDeBrujin).toHoAS
  | .exis p => .exis fun x => (p.subst ⟨0, Nat.zero_lt_succ _⟩ x.toDeBrujin).toHoAS

  | .conj a b => .conj a.toHoAS b.toHoAS
  | .disj a b => .disj a.toHoAS b.toHoAS
  | .imp  a b => .imp  a.toHoAS b.toHoAS
  | .iff  a b => .iff  a.toHoAS b.toHoAS
  | .neg v => .neg v.toHoAS
termination_by f => f.sz
decreasing_by
all_goals simp_wf
all_goals (try { dsimp [sz]; omega })
all_goals rw [subst.sz]
all_goals exact Nat.lt_succ_self _

