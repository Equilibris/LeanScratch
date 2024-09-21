import Mathlib.Data.Rel

lemma Relation.transGenMap
    {R₁ : α → α → Prop}
    {R₂ : β → β → Prop}
    {m : α → β}
    (f : {a b : α} → R₁ a b → R₂ (m a) (m b))
    (h : Relation.TransGen R₁ x y)
    : Relation.TransGen R₂ (m x) (m y) :=
  h.rec (.single $ f ·) (fun _ body ih => .tail ih $ f body)

lemma Relation.reflTransGenMap
    {R₁ : α → α → Prop}
    {R₂ : β → β → Prop}
    {m : α → β}
    (f : {a b : α} → R₁ a b → R₂ (m a) (m b))
    (h : Relation.ReflTransGen R₁ x y)
    : Relation.ReflTransGen R₂ (m x) (m y) :=
  h.rec .refl (fun _ body ih => .tail ih $ f body)


lemma Relation.transGenMap'
    {R₁ : α → α → Prop}
    {R₂ : β → β → Prop}
    {m : α → β}
    (f : {a b : α} → R₁ a b → R₂ (m a) (m b))
    (h : Relation.TransGen R₁ x y)
    : Relation.TransGen R₂ (m x) (m y) :=
  h.rec (.single $ f ·) (fun _ body ih => .tail ih $ f body)

