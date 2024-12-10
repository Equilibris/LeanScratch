import LeanScratch.Semantics.L2.Stx
import LeanScratch.Semantics.L2.Red
import LeanScratch.Semantics.L2.Typed

namespace L2

section Q19

inductive Expr.FV : Expr → ℕ → Prop
  | opl : FV lhs n → FV (.op lhs o rhs) n
  | opr : FV rhs n → FV (.op lhs o rhs) n

  | eifc : FV c n → FV (.eif c t f) n
  | eift : FV t n → FV (.eif c t f) n
  | eiff : FV f n → FV (.eif c t f) n

  | assign : FV e n → FV (.assign addr e) n

  | seqa : FV a n → FV (.seq a b) n
  | seqb : FV b n → FV (.seq a b) n

  | appfn  : FV a n → FV (.app a b) n
  | apparg : FV b n → FV (.app a b) n

  | bvar : FV (.bvar idx) idx
  | abs : FV body n.succ → FV (.abs t body) n
  | letValVal : FV val n      → FV (.letVal t val _) n
  | letValIn  : FV vin n.succ → FV (.letVal t _ vin) n
  | letRecValVal : FV val n.succ → FV (.letRecVal t val _) n
  | letRecValIn  : FV vin n.succ → FV (.letRecVal t _ vin) n

abbrev Ex1 := (Expr.op (.bvar 0) .add (.app (.abs .int (.bvar 2)) (.int 2)))
abbrev Ex1.Set : Set ℕ := {0, 1}

-- cant be bothered to show the iff
theorem Ex1.P : ∀ x ∈ Ex1.Set, Ex1.FV x :=
  fun x hx => by
    rcases hx with (hx|hx) <;> simp_all only [Set.mem_singleton_iff]
    · exact .opl .bvar
    · exact .opr $ .appfn $ .abs $ .bvar

abbrev Ex2 := (Expr.op (.bvar 0) .add (.abs .int (.bvar 2)))
abbrev Ex2.Set : Set ℕ := {0, 1}

theorem Ex2.P : ∀ x ∈ Ex2.Set, Ex2.FV x :=
  fun x hx => by
    rcases hx with (hx|hx) <;> simp_all only [Set.mem_singleton_iff]
    · exact .opl .bvar
    · exact .opr $ .abs $ .bvar

abbrev Ex3 := (Expr.abs .int $ .abs .int $ .abs .int $ .bvar 0)

theorem Ex3.P : ∀ n, ¬Ex3.FV n :=
  fun x hx => by
    cases hx; rename_i hx
    cases hx; rename_i hx
    cases hx; rename_i hx
    cases hx

abbrev Ex4 := Expr.deref "l1"
theorem Ex4.P : ∀ n, ¬Ex4.FV n := fun x hx => by cases hx

end Q19

section Q21

namespace FOrder

inductive TopTy
  | bool
  | int
  | void
deriving DecidableEq, Repr

inductive Ty
  | top (t : TopTy)
  | arr (arg : TopTy) (ret : Ty)
deriving DecidableEq, Repr

end Q21.FOrder

section Q23
theorem BvarShift.gen (hMain : TySpec Γ (Γ₂ ++ Γ') body tout)
    : TySpec Γ (Γ₂ ++ Γlead ++ Γ') (body.bvarShift Γlead.length Γ₂.length) tout :=
  match body with
  | .bool b => by
    cases hMain
    exact .bool
  | .int i => by
    cases hMain
    exact .int
  | .skip => by
    cases hMain
    exact .skip
  | .op lhs .add rhs => by
    cases hMain
    rename_i lhsIh rhsIh
    exact .op_add (BvarShift.gen lhsIh) (BvarShift.gen rhsIh)
  | .op lhs .gte rhs => by
    cases hMain
    rename_i lhsIh rhsIh
    exact .op_gte (BvarShift.gen lhsIh) (BvarShift.gen rhsIh)
  | .eif cond t f => by
    cases hMain
    rename_i condIh tIh fIh
    exact .eif (BvarShift.gen condIh) (BvarShift.gen tIh) (BvarShift.gen fIh)
  | .ewhile cond e => by
    cases hMain
    rename_i condIh eIh
    exact .ewhile (BvarShift.gen condIh) (BvarShift.gen eIh)
  | .assign addr e => by
    cases hMain
    rename_i p eIh
    exact .assign p (BvarShift.gen eIh)
  | .deref addr => by
    cases hMain
    exact .deref (by assumption)
  | .seq a b => by
    cases hMain
    rename_i aIh bIh
    exact .seq (BvarShift.gen aIh) (BvarShift.gen bIh)
  | .bvar idx => by
    cases hMain; case ref p =>
    dsimp [Expr.bvarShift]
    split
    <;> rename_i x
    · rw [List.append_assoc]
      rw [List.getElem?_append x] at p
      exact .ref (by rwa [List.getElem?_append x])
    · simp only [not_lt] at x
      rw [List.getElem?_append_right x] at p
      exact .ref (by
      rw [List.append_assoc, List.getElem?_append_right (Nat.le_add_right_of_le x)]
      have h : Γlead.length ≤ idx + Γlead.length - Γ₂.length := by omega
      rwa [
        List.getElem?_append_right h,
        Nat.sub_right_comm,
        Nat.add_sub_assoc (Nat.le_refl _) _,
        Nat.sub_self
      ])
  | .abs ty body => by
    cases hMain
    rename_i _ bodyIh
    change TySpec _ (ty :: Γ₂ ++ Γ') _ _ at bodyIh
    exact .abs (BvarShift.gen bodyIh)
  | .app fn arg => by
    cases hMain
    rename_i argIh fnIh
    exact .app (BvarShift.gen fnIh) (BvarShift.gen argIh)
  | .letVal t' val body => by
    cases hMain
    rename_i valIh bodyIh
    change TySpec _ (t' :: Γ₂ ++ Γ') _ _ at bodyIh
    exact .letVal (BvarShift.gen valIh) (BvarShift.gen bodyIh)
  | .letRecVal _ val body => by
    cases hMain; next valIh bodyIh =>
    change TySpec _ (_ :: Γ₂ ++ Γ') _ _ at bodyIh
    change TySpec _ (_ :: _ :: Γ₂ ++ Γ') _ _ at valIh
    exact .letRecValFn (BvarShift.gen valIh) (BvarShift.gen bodyIh)

theorem Subst.gen (hTy : TySpec Γ Γ' e t) (hMain : TySpec Γ (Γlead ++ (t :: Γ')) body tout)
    : TySpec Γ (Γlead ++ Γ') (body.replace Γlead.length e) tout :=
  match body with
  | .bool b => by
    cases hMain
    exact .bool
  | .int i => by
    cases hMain
    exact .int
  | .skip => by
    cases hMain
    exact .skip
  | .op lhs .add rhs => by
    cases hMain
    rename_i lhsIh rhsIh
    exact .op_add (Subst.gen hTy lhsIh) (Subst.gen hTy rhsIh)
  | .op lhs .gte rhs => by
    cases hMain
    rename_i lhsIh rhsIh
    exact .op_gte (Subst.gen hTy lhsIh) (Subst.gen hTy rhsIh)
  | .eif cond t f => by
    cases hMain
    rename_i condIh tIh fIh
    exact .eif (Subst.gen hTy condIh) (Subst.gen hTy tIh) (Subst.gen hTy fIh)
  | .ewhile cond e => by
    cases hMain
    rename_i condIh eIh
    exact .ewhile (Subst.gen hTy condIh) (Subst.gen hTy eIh)
  | .assign addr e => by
    cases hMain
    rename_i p eIh
    exact .assign p (Subst.gen hTy eIh)
  | .deref addr => by
    cases hMain
    exact .deref (by assumption)
  | .seq a b => by
    cases hMain
    rename_i aIh bIh
    exact .seq (Subst.gen hTy aIh) (Subst.gen hTy bIh)
  | .bvar idx => by
    cases hMain; case ref p =>
    dsimp [Expr.replace, Expr.replace.bvar]
    split
    <;> rename_i x
    <;> simp only [Nat.compare_eq_eq, Nat.compare_eq_lt, Nat.compare_eq_gt] at x
    · exact .ref (by rwa [List.getElem?_append x] at p ⊢)
    · subst x
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at p
      subst p
      exact BvarShift.gen (Γ₂ := []) hTy
    · refine .ref ?_
      rw [List.getElem?_append_right (Nat.le_of_succ_le x)] at p
      rw [List.getElem?_append_right (Nat.le_sub_one_of_lt x), Nat.sub_right_comm]
      change ([_] ++ _)[_]? = _ at p
      have : [t].length ≤ idx - Γlead.length := Nat.le_sub_of_add_le' x
      rwa [List.getElem?_append_right this] at p
  | .abs ty body => by
    cases hMain
    rename_i _ bodyIh
    change TySpec _ (ty :: Γlead ++ t :: Γ') _ _ at bodyIh
    exact .abs (Subst.gen hTy bodyIh)
  | .app fn arg => by
    cases hMain
    rename_i argIh fnIh
    exact .app (Subst.gen hTy fnIh) (Subst.gen hTy argIh)
  | .letVal t' val body => by
    cases hMain
    rename_i valIh bodyIh
    change TySpec _ (t' :: Γlead ++ t :: Γ') _ _ at bodyIh
    exact .letVal (Subst.gen hTy valIh) (Subst.gen hTy bodyIh)
  | .letRecVal _ val body => by
    cases hMain; next valIh bodyIh =>
    change TySpec _ (_ :: Γlead ++ t :: Γ') _ _ at bodyIh
    change TySpec _ (_ :: _ :: Γlead ++ t :: Γ') _ _ at valIh
    exact .letRecValFn (Subst.gen hTy valIh) (Subst.gen hTy bodyIh)

theorem Subst : TySpec Γ Γ' e t → TySpec Γ (t :: Γ') body tout → TySpec Γ Γ' (body.replace 0 e) tout
  := Subst.gen (Γlead := [])
end Q23

section Q24

theorem TypePreservation (tyPre : TySpec Γ Γ' e t) (hMain : Red ⟨e, s1⟩ ⟨e', s2⟩) : TySpec Γ Γ' e' t :=
  match e with
  | .bool b => by
    cases hMain
  | .int i => by
    cases hMain
  | .skip => by
    cases hMain
  | .op lhs .add rhs => by
    cases hMain <;> cases tyPre
    · exact .int
    case op1 ha lhs rhs =>
      exact .op_add (TypePreservation lhs ha) rhs
    case op2 hb lhs rhs => 
      exact .op_add lhs (TypePreservation rhs hb)
  | .op lhs .gte rhs => by
    cases hMain <;> cases tyPre
    · exact .bool
    case op1 ha lhs rhs =>
      exact .op_gte (TypePreservation lhs ha) rhs
    case op2 hb lhs rhs => 
      exact .op_gte lhs (TypePreservation rhs hb)
  | .eif cond t f => by
    cases hMain <;> cases tyPre
    case if_t => assumption
    case if_f => assumption
    case if_cond ha cond t f =>
      exact .eif (TypePreservation cond ha) t f
  | .ewhile cond e =>
    match tyPre with
    | .ewhile cond e => by
      cases hMain
      obtain rfl : t = .void := by
        cases tyPre
        rfl
      exact .eif cond (.seq e tyPre) .skip
  | .assign addr e => by
    cases hMain <;> cases tyPre
    · exact .skip
    case assign ha z ty =>
      exact .assign z (TypePreservation ty ha)
  | .deref addr => by
    cases hMain
    cases tyPre
    exact .int
  | .seq a b => by
    cases hMain <;> cases tyPre
    · assumption
    case seq ha tya tyb =>
      exact .seq (TypePreservation tya ha) tyb
  | .bvar idx => by
    cases hMain
  | .abs ty body => by
    cases hMain
  | .app fn arg => by
    cases hMain <;> cases tyPre
    case app1 ha _ argTy bodyTy =>
      exact .app (TypePreservation bodyTy ha) argTy
    case app2  ha _ argTy bodyTy =>
      exact .app bodyTy (TypePreservation argTy ha)
    case fn argTy bodyTy =>
      cases bodyTy; next bodyTy =>
      exact Subst argTy bodyTy
  | .letVal t' val body => by
    cases hMain <;> cases tyPre
    case let1 ha argTy bodyTy => exact .letVal (TypePreservation argTy ha) bodyTy
    case let2 argTy bodyTy =>
      exact Subst argTy bodyTy
  | .letRecVal _ val body => by
    cases hMain

/-- info: 'L2.TypePreservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TypePreservation 

end Q24

namespace Q28

inductive TyZ : Type 1
  | unit
  | prod (a b : TyZ)
  | sum  (a b : TyZ)
  | variant (t : Type) (record : t → TyZ)

inductive Stx : TyZ → Type 1
  | unit : Stx .unit
  | prod (a : Stx aT) (b : Stx bT) : Stx (.prod aT bT)
  | inl bT (x : Stx aT) : Stx (.prod aT bT)
  | inr aT (x : Stx bT) : Stx (.prod aT bT)
  | variant (v : t) (x : Stx (mapping v)) : Stx (.variant t mapping)

end Q28

end L2

namespace y2003p5q11

inductive Ty
  | int
  | unit
  | arr (arg ret : Ty)

inductive Expr
  | int (i : Int) -- In implementation we need to specify overflow behaviour
  | skip
  | assign (l : String) (body : Expr)
  | deref (l : String)
  | abs (ty : Ty) (body : Expr)
  | app (fn arg : Expr)
  | bvar (idx : ℕ)

namespace Expr

def bvarShift (shift skip : ℕ) : Expr → Expr
  | .bvar n => .bvar $ if n < skip then n else n + shift
  | .app a b => .app (a.bvarShift shift skip) (b.bvarShift shift skip)
  | .abs ty body => .abs ty (body.bvarShift shift skip.succ)
  | .assign l body => .assign l (body.bvarShift shift skip)
  | x@(.int _) | x@(.deref _) | x@(.skip) => x

def replace.bvar (bvarId idx_shift : ℕ) (replace : Expr) : Expr :=
  match compare bvarId idx_shift with
  | .lt => .bvar bvarId
  | .eq => replace.bvarShift idx_shift 0
  | .gt => .bvar bvarId.pred

-- Replace also needs to add idx to every value within replace to ensure that the binders still point towards the right points
def replace (idx_shift : ℕ) (body replace : Expr) : Expr := match body with
  | .bvar n => Expr.replace.bvar n idx_shift replace
  | .app fn arg => .app (fn.replace idx_shift replace) (arg.replace idx_shift replace)
  | .abs ty v => .abs ty (v.replace idx_shift.succ replace)
  | .assign l body => .assign l (body.replace idx_shift replace)
  | x@(.int _) | x@(.deref _) | x@(.skip) => x

def β (body repl : Expr) : Expr := (body.replace 0 repl)

end Expr

abbrev Ctx := AList (fun (_ : String) => Int)

def change (v : α) : ℕ → List α → List α
  | 0,    _ :: tl =>  v :: tl
  | n+1, hd :: tl => hd :: (change v n tl)
  | _, [] => []

def reduce : Expr → Ctx → Option (Expr × Ctx)
  | .deref l, s => (match s.lookup l with
      | .some v => .some (.int v, s)
      | .none => .some (.int 0, s.insert l 0))
  | .assign l e, s => (match e with
    | .int n => .some ⟨.skip, s.insert l n⟩
    | e => (reduce e s).map (fun ⟨e, s⟩ => ⟨.assign l e, s⟩))

  | .app e1 e2, s => (match e1 with
    | .abs _ e1 => .some ⟨e1.β e2, s⟩
    | e1 => (reduce e1 s).map (fun ⟨e1, s⟩ => ⟨.app e1 e2, s⟩ ) )

  | .int _, _ | .skip, _ | .bvar _, _ | .abs _ _ , _ => .none

inductive Red : Expr → Ctx → Expr → Ctx → Prop
  | deref_hit  : s.lookup l = .some v → Red (.deref l) s (.int v) s
  | deref_miss : s.lookup l = .none   → Red (.deref l) s (.int 0) (s.insert l 0)
  | assign_congr : Red e s e' s' → Red (.assign l e) s (.assign l e') s'
  | assign_write : Red (.assign l (.int v)) s .skip (s.insert l v)
  | app_congr : Red e s e' s' → Red (.app e arg) s (.app e' arg) s'
  | beta : Red (.app (.abs _ e1) arg) s (e1.β arg) s

theorem reduce_Red (h : reduce e s = .some ⟨e', s'⟩) : Red e s e' s' := match e with
  | .deref l => by
    dsimp [reduce] at h
    split at h
    <;> rename_i h'
    <;> obtain ⟨rfl, rfl⟩ := h
    · exact .deref_hit  h'
    · exact .deref_miss h'
  | .assign l e => by
    unfold reduce at h
    split at h
    <;> rename_i h'
    <;> simp only [Option.some.injEq, Prod.mk.injEq] at h
    · obtain ⟨rfl, rfl⟩ := h
      exact .assign_write
    · dsimp [Option.map] at h
      split at h
      · rename_i hx
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .assign_congr $ reduce_Red hx
      · contradiction
  | .app fn arg => by
    unfold reduce at h
    split at h
    · obtain ⟨rfl, rfl⟩ := h
      exact .beta
    · dsimp [Option.map] at h
      split at h
      · rename_i hx
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .app_congr $ reduce_Red hx
      · contradiction

theorem Red_reduce (h : Red e s e' s' ) : reduce e s = .some ⟨e', s'⟩ := match e with
  | .deref l => by
    cases h <;> simp_all only [reduce]
  | .app fn arg
  | .assign l e => by
    cases h
    · unfold reduce
      split
      · contradiction
      · rename_i h' _ _
        simp only [Option.map, Red_reduce h']
    · rfl

-- Turns out these are really clean one-liners, they are also kinda trivial
theorem not_Red_reduce (h : ∀ {e' s'}, ¬Red e s e' s') : reduce e s = .none :=
  Classical.byContradiction
    (· |> Option.ne_none_iff_exists.mp |>.choose_spec.symm |> reduce_Red |> h)
theorem not_reduce_Red (h : reduce e s = .none) : ∀ {e' s'}, ¬Red e s e' s' :=
  Classical.byContradiction
    (· |> Classical.not_not.mp |> Red_reduce |>.symm.trans h |> Option.noConfusion)

end y2003p5q11
