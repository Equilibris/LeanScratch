import LeanScratch.Computation.RegMachine

namespace Comp

variable {InsA InsB} [Fintype2 InsA] [Fintype2 InsB]

def subroutine
    {r t : RegTree}
    (inM : RegMachine r InsA)
    (rmapper : r.toIdx → t.toIdx)
    (imapper : InsA → InsB)
    (hltStepper : InsB)
    (x : InsA)
    : RegMachine.Ins t InsB :=
  match inM x with
  | .inc r next =>
    let next := match inM next with
      | .hlt => hltStepper
      | _    => imapper next
    .inc (rmapper r) next
  | .dec r nz z =>
    let nz := match inM nz with
      | .hlt => hltStepper
      | _    => imapper nz
    let z  := match inM z with
      | .hlt => hltStepper
      | _    => imapper z
    .dec (rmapper r) nz z
  | .hlt => .hlt -- This case should be handled differently maybe

theorem RegMachine.step.none_hlt [Fintype2 L] {inM : RegMachine r L}
    (h : RegMachine.Config.step inM ⟨view, s⟩ = none)
    : inM s = .hlt :=
  match heq : inM s with
  | .hlt => rfl
  | .inc _ _ | .dec _ _ _ => by
    simp only [Config.step, heq] at h
    <;> split at h
    <;> exact Option.noConfusion h

def updateImageVec
    {t : RegTree}
    (rmapper : Fin2 n → t.toIdx)
    (src : Vec Nat n)
    (dst : t.toStore)
    : t.toStore :=
  match src with
  | %[] => dst
  | hd %:: tl => t.set (updateImageVec (rmapper ∘ Fin2.fs) tl dst) (rmapper .fz) hd

abbrev updateImageVec_alt
    {t : RegTree}
    (rmapper : Fin2 n → t.toIdx)
    (src : Vec Nat n)
    (dst : t.toStore)
    : t.toStore :=
  t.set_many dst (Fin2.instFintype2.elems.map (fun x => ⟨rmapper x, src.lookup x⟩))

theorem updateImageVec_eq_alt
    {t : RegTree}
    {rmapper : Fin2 n → t.toIdx}
    {src : Vec Nat n}
    {dst : t.toStore}
    : updateImageVec rmapper src dst =
      updateImageVec_alt rmapper src dst :=
  match n, src with
  | 0, %[] => by simp [updateImageVec_alt, updateImageVec, Fin2.instFintype, RegTree.set_many]
  | n+1, hd %:: tl => by
    set_option pp.all true in
    dsimp [updateImageVec, updateImageVec_alt, Fintype2.elems, RegTree.set_many, Vec.lookup]
    rw [List.map_map]
    congr
    change _ = updateImageVec_alt _ _ _
    exact updateImageVec_eq_alt

/- /-- error: (kernel) deep recursion detected -/ -/
/- #guard_msgs in -/
/- abbrev UI_alt -/
/-     {r t : RegTree} -/
/-     (rmapper : r.toIdx → t.toIdx) -/
/-     (src : r.toStore) -/
/-     (dst : t.toStore) -/
/-     : t.toStore := -/
/-   t.set_many dst (RegTree.instFintype2.elems.map (fun x => ⟨rmapper x, r.lookup src x⟩)) -/

def updateImage
    {r t : RegTree}
    (rmapper : r.toIdx → t.toIdx)
    (src : r.toStore)
    (dst : t.toStore)
    : t.toStore :=
  match r, src with
  | .lf _, v => updateImageVec rmapper v dst
  | .br _ _, ⟨lsrc, rsrc⟩ =>
    (updateImage (rmapper ∘ Sum.inr) rsrc dst) |>
    (updateImage (rmapper ∘ Sum.inl) lsrc ·)

theorem updateImage_eq_alt
    {r t : RegTree}
    {rmapper : r.toIdx → t.toIdx}
    {src : r.toStore}
    {dst : t.toStore}
    : updateImage rmapper src dst =
      t.set_many dst (RegTree.instFintype2.elems.map (fun x => ⟨rmapper x, r.lookup src x⟩)) :=
  match r, src with
  | .lf _, v => updateImageVec_eq_alt
  | .br _ _, ⟨a, b⟩ => by
    dsimp [updateImage, Fintype2.elems]
    rw [List.map_append, List.map_map, List.map_map]
    rw [updateImage_eq_alt, updateImage_eq_alt]
    rw [RegTree.set_many.comp]
    rfl

theorem updateImage.comm_inj
    {r l t : RegTree}
    {rmapper : (r.br l).toIdx → t.toIdx}
    {rs : r.toStore}
    {ls : l.toStore}
    {dst : t.toStore}
    (hInj : Function.Injective rmapper)
    : updateImage (rmapper ∘ Sum.inr) ls (updateImage (rmapper ∘ Sum.inl) rs dst) =
      updateImage (rmapper ∘ Sum.inl) rs (updateImage (rmapper ∘ Sum.inr) ls dst) := by
  rw [updateImage_eq_alt, updateImage_eq_alt, RegTree.set_many.comp, updateImage_eq_alt, updateImage_eq_alt, RegTree.set_many.comp]
  apply RegTree.set_many.perm _ (List.perm_append_comm)
  simp only [Function.comp_apply, List.map_append, List.map_map]
  change List.Nodup ((List.map (rmapper ∘ Sum.inr) _) ++ (List.map (rmapper ∘ Sum.inl) _))
  apply List.Nodup.append
  case dj =>
    simp only [List.Disjoint, List.mem_map, Function.comp_apply, imp_false, not_exists, not_and,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun _ _ _ _ h => Sum.noConfusion (hInj h)
  all_goals apply List.Nodup.map
  <;> (try exact Fintype2.nodup) <;> apply Function.Injective.comp hInj
  · exact @Sum.inr.inj _ _
  · exact @Sum.inl.inj _ _

theorem updateImageVec.inc_slide
    {t : RegTree}
    {rmapper : Fin2 n → t.toIdx}
    {iInitStore outerStore}
    : RegMachine.inc (rmapper reg) (updateImageVec rmapper iInitStore outerStore) =
      updateImageVec rmapper       (RegMachine.inc_vec reg iInitStore) outerStore :=
  match n, iInitStore, reg with
  | n+1, hd %:: tl, .fz => by dsimp [RegMachine.inc_vec, updateImageVec]; sorry
  | n+1, hd %:: tl, .fs idx => by
    simp [updateImageVec]
    sorry

/- theorem Comp.updateImage.extracted_1 -/
/-     {r t : RegTree} {rmapper : r.toIdx → t.toIdx} {iInitStore : r.toStore} -/
/-     {outerStore : t.toStore} {reg : r.toIdx} {x : t.toIdx} (h : x = rmapper reg) -/
/-     : t.set (updateImage rmapper iInitStore outerStore) x (t.lookup (updateImage rmapper iInitStore outerStore) x).succ = -/
/-       updateImage rmapper (r.set iInitStore reg (r.lookup iInitStore reg).succ) outerStore := -/
/-   match r, t, x, reg with -/
/-   | _, _, _, _ => sorry -/

theorem updateImage.inc_slide
    {r t : RegTree}
    {rmapper : r.toIdx → t.toIdx}
    {iInitStore outerStore}
    {reg : r.toIdx}
    : RegMachine.inc (rmapper reg) (updateImage rmapper iInitStore outerStore) =
      updateImage rmapper (RegMachine.inc reg iInitStore) outerStore := by
  rw [RegMachine.inc.eq_set]
  rw [RegMachine.inc.eq_set]
  sorry
  /- match r, reg, iInitStore with -/
  /- | .lf _, reg, store => sorry -/
  /- | .br _ _, .inl reg, ⟨l, r⟩ => by -/
  /-   dsimp [RegMachine.inc] -/
  /-   conv => -/
  /-     lhs; -/
  /-     dsimp [updateImage, RegMachine.inc] -/
  /-   /- rw [updateImage.inc_slide] -/ -/
  /-   sorry -/
  /- | .br _ _, .inr reg, ⟨l, r⟩ => by -/
  /-   sorry -/

theorem subroutine.forward
    {r t : RegTree}
    {prog : RegMachine t InsB}

    {inM : RegMachine r InsA}
    {rmapper : r.toIdx → t.toIdx}
    {imapper : InsA → InsB}

    {iInitStore iEndStore outerStore}

    -- the following theorems should all be solvable with large simps
    (hIsSub : prog ∘ imapper = subroutine inM rmapper imapper hltStepper)

    (hRInj : Function.Injective rmapper)
    (hIInj : Function.Injective imapper)

    (hInTW : inM.TW ⟨iInitStore, startS⟩ ⟨iEndStore, endS⟩)
    (hStartNotHlt : inM startS ≠ .hlt)

    : prog.StepsTo ⟨updateImage rmapper iInitStore outerStore, imapper startS⟩
                   ⟨updateImage rmapper iEndStore  outerStore, hltStepper⟩ := by
  rcases hInTW with ⟨w, term, v⟩
  induction w generalizing startS iInitStore
  · obtain ⟨rfl, rfl⟩ := (RegMachine.Config.mk.injEq _ _ _ _).mp $ (Option.some.injEq _ _).mp term
    exact (hStartNotHlt $ RegMachine.step.none_hlt v).elim
  case succ n ih =>
    obtain ⟨⟨imStore, imState⟩, stepper, p⟩ := Option.bind_eq_some.mp term
    clear term

    exists n+1
    simp only [RegMachine.Config.step_n]
    apply Option.bind_eq_some.mpr
    dsimp [RegMachine.Config.step, subroutine]
    simp [Function.funext_iff] at hIsSub
    rw [hIsSub]
    dsimp [subroutine]
    cases heq : inM startS
    <;> (try exact (hStartNotHlt heq).elim)
    <;> rename_i reg nextins
    <;> by_cases hNextEq : inM nextins = .hlt
    · clear ih
      use ⟨RegMachine.inc (rmapper reg) (updateImage rmapper iInitStore outerStore), hltStepper⟩
      simp [hNextEq]
      simp only [RegMachine.Config.step, heq, Option.some.injEq, RegMachine.Config.mk.injEq] at stepper
      rcases stepper with ⟨rfl, rfl⟩
      obtain rfl : n = 0 := by
        cases n
        · rfl
        · simp [RegMachine.Config.step_n, RegMachine.Config.step, hNextEq] at p
      simp_all only [ne_eq, not_false_eq_true, RegMachine.Config.step_n.zero, Option.some.injEq,
        RegMachine.Config.mk.injEq, and_true]
      rcases p with ⟨rfl, rfl⟩
      sorry
      /- by_cases hInImage : ∃ v', v = rmapper v' -/
      /- sorry -/
      /- · have := hNeqStores _ hInImage -/
      /-   sorry -/
    · sorry
    · sorry
    · sorry

