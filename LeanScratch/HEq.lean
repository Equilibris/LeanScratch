@[elab_as_elim]
def HEq.dependentRw
    {α : Sort _} {a b : α}
    {submotive : α → Sort _} {motive : (base : α) → submotive base → Sort _}
    {x : submotive a} {y : submotive b}
    (hParEq : a = b)
    (hEq : HEq x y)
    (src : motive a x)
    : motive b y := by
  subst hParEq
  subst hEq
  exact src

@[elab_as_elim]
def HEq.dependentRw'
    {α : Sort _} {a b : α}
    {submotive : α → Sort _} {motive : (base : α) → submotive base → Sort _}
    {x : submotive a} {y : submotive b}
    (hParEq : a = b)
    (hEq : HEq x y)
    (src : motive a x)
    : motive b y := by
  subst hParEq
  subst hEq
  exact src
