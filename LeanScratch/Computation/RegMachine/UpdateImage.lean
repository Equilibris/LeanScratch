import LeanScratch.Computation.RegMachine

namespace Comp

def updateImageVec
    {t : RegTree}
    (rmapper : Fin2 n → t.toIdx)
    (src : Vec Nat n)
    (dst : t.toStore)
    : t.toStore :=
  match src with
  | %[] => dst
  | hd %:: tl => t.set (updateImageVec (rmapper ∘ Fin2.fs) tl dst) (rmapper .fz) hd

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

theorem updateImage.lookup.lem {r t : RegTree} {rmapper : r.toIdx → t.toIdx} {iInitStore : r.toStore}
  {s : List r.toIdx} {outerStore : t.toStore} {reg : r.toIdx} (hInj : Function.Injective rmapper)
  (hMem : reg ∈ s)
  (hMem' : rmapper reg ∈ List.map rmapper s)
  : t.lookup (t.set_many outerStore (List.map (fun x ↦ (rmapper x, r.lookup iInitStore x)) s)) (rmapper reg) =
    r.lookup iInitStore reg := match s with
  | [] => ((List.mem_nil_iff reg).mp hMem).elim
  | hd :: tl => by
    dsimp [RegTree.set_many]
    by_cases h : reg = hd
    · subst h
      rw [RegTree.lookup_set_eq]
    · rw [RegTree.lookup_set_ne (h $ hInj ·.symm)]
      apply updateImage.lookup.lem hInj (List.mem_of_ne_of_mem h hMem)
      simp_all

theorem updateImage.lookup
    {r t : RegTree}
    {rmapper : r.toIdx → t.toIdx}
    {iInitStore outerStore}
    {reg : r.toIdx}
    (hInj : Function.Injective rmapper)
    : t.lookup (updateImage rmapper iInitStore outerStore) (rmapper reg) =
      r.lookup iInitStore reg := by
  rw [updateImage_eq_alt]
  let regMem : reg ∈ _ := Fintype2.complete reg
  let rMapperReg : rmapper reg ∈ List.map rmapper _ := List.mem_map_of_mem rmapper regMem
  exact updateImage.lookup.lem hInj regMem rMapperReg

theorem updateImage.set
    {r t : RegTree}
    {rmapper : r.toIdx → t.toIdx}
    {iInitStore outerStore}
    {reg : r.toIdx}
    (hInj : Function.Injective rmapper)
    : t.set (updateImage rmapper iInitStore outerStore) (rmapper reg) v =
      updateImage rmapper (r.set iInitStore reg v) outerStore := by
  ext z
  by_cases h : z = rmapper reg
  · subst h
    rw [updateImage.lookup hInj]
    simp
  · have hSymm : rmapper reg ≠ z := h ∘ Eq.symm
    rw [RegTree.lookup_set_ne hSymm]
    by_cases h : ∃ k, z = rmapper k
    · rcases h with ⟨z, rfl⟩
      rw [updateImage.lookup hInj, updateImage.lookup hInj]
      rw [RegTree.lookup_set_ne]
      exact fun a => h $ a.rec rfl
    · rw [not_exists] at h
      rw [updateImage_eq_alt, updateImage_eq_alt]
      rw [RegTree.lookup_set_many_none, RegTree.lookup_set_many_none]
      <;> simp only [Nat.succ_eq_add_one, List.map_map, List.mem_map, Fintype2.complete,
        Function.comp_apply, true_and, not_exists]
      <;> exact fun z eq => h z eq.symm

theorem updateImage.inc_slide
    {r t : RegTree}
    {rmapper : r.toIdx → t.toIdx}
    {iInitStore outerStore}
    {reg : r.toIdx}
    (hInj : Function.Injective rmapper)
    : RegMachine.inc (rmapper reg) (updateImage rmapper iInitStore outerStore) =
      updateImage rmapper (RegMachine.inc reg iInitStore) outerStore := by
  rw [RegMachine.inc.eq_set,
      RegMachine.inc.eq_set,
      updateImage.lookup hInj,
      updateImage.set hInj]

theorem updateImage.dec_slide
    {r t : RegTree}
    {rmapper : r.toIdx → t.toIdx}
    {iInitStore outerStore}
    {reg : r.toIdx}
    (hInj : Function.Injective rmapper)
    : RegMachine.dec (rmapper reg) (updateImage rmapper iInitStore outerStore) =
      (RegMachine.dec reg iInitStore).map (updateImage rmapper · outerStore)
      := by
  by_cases h : ∃ z, RegMachine.dec reg iInitStore = some z
  · -- Begin intense bit of proof
    have ⟨k, hKEq⟩ := Nat.exists_eq_succ_of_ne_zero
        $ (not_congr RegMachine.dec_none_iff_lookup_z).mp
        $ Option.ne_none_iff_exists'.mpr h
    have : t.lookup (updateImage rmapper iInitStore outerStore) (rmapper reg) = k.succ :=
      Eq.trans (updateImage.lookup hInj) hKEq
    have ⟨w', hBigEqSome⟩ := Option.ne_none_iff_exists'.mp
        $ (not_congr RegMachine.dec_none_iff_lookup_z).mpr
        (Nat.noConfusion $ Eq.trans ·.symm this)
    rcases h with ⟨w, hEqSome⟩
    -- end intense bit of proof
    rw [hEqSome,    RegMachine.dec.eq_set hEqSome,
        hBigEqSome, RegMachine.dec.eq_set hBigEqSome]
    clear *-hInj
    apply (Option.some.injEq _ _).mpr
    dsimp
    rw [updateImage.lookup hInj, updateImage.set hInj]
  · simp only [← Option.ne_none_iff_exists', ne_eq, not_not] at h
    have : t.lookup (updateImage rmapper iInitStore outerStore) (rmapper reg) = 0 :=
      Eq.trans (updateImage.lookup hInj) (RegMachine.dec_none_iff_lookup_z.mp h)
    rw [RegMachine.dec_none_iff_lookup_z.mpr this, h]
    rfl
