/-
coinductive CoList (α : Type _) :=
  | nil
  | cons (hd : α) (tl : CoList α)
-/

inductive CoList.Shape.{u, v} (α : Type u) (CoList : Type u → Type v)
  | nil
  | cons (hd : α) (tl : CoList α)

def CoList.{u, v} (α : Type u) : Type (max (u + 1) (v + 1)) := (t : Type u → Type v) × t α × (t α → CoList.Shape α t)

def CoList.dest.{u, v} {α : Type u} (v : CoList.{u, v} α) : Shape.{u, max (u + 1) (v + 1)} α CoList.{u, v} :=
  let ⟨x, v, trans⟩ := v
  match trans v with
  | .nil => .nil
  | .cons hd tl => .cons hd ⟨x, tl, trans⟩

def CoList.ndcorec.{u, v} (v : ζ) (f : ζ → CoList.Shape.{u, v} α (fun _ => ζ)) : CoList α := ⟨fun _ => ζ, v, f⟩


