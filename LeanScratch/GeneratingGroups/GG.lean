
namespace GGMod

inductive GG (α : Type _)
  | unit
  | obj (v : α)
  | inv (v : α)
  | app (a b : GG α)

instance : Inhabited (GG α) := ⟨.unit⟩

abbrev rTy α := (GG α) → (GG α) → Prop

end GGMod
