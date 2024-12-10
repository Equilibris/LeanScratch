inductive Ty
  | int
  | record : List Ty → Ty
  | fn : Ty → Ty → Ty

inductive PairWise (R : α → β → Prop) : List α → List β → Prop
  | nil : PairWise R [] []
  | cons : R a b → PairWise R as bs → PairWise R (a :: as) (b :: bs)

inductive TySub : Ty → Ty → Prop
  | int : TySub .int .int
  | fn (arg : TySub b1 a1) (ret : TySub a2 b2) :
    TySub (.fn a1 a2) (.fn b1 b2)
  | record :
    PairWise TySub as bs →
    TySub (.record as) (.record bs)

theorem TySub.refl : TySub a a := 
  match a with
  | .int => .int
  | .fn a b => .fn TySub.refl TySub.refl
  | .record vs => 
    let rec x vs : PairWise TySub vs vs := match vs with
      | [] => .nil
      | hd :: tl => .cons TySub.refl (x tl)
    .record (x vs)

