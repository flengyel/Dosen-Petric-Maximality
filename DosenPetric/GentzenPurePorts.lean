module

public import DosenPetric.GentzenPureFormulas

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- A signed literal occurrence reached through only the indicated connective.
Left and right constructors keep repeated literal occurrences distinct. -/
inductive PurePort (o : Op) : NormalForm P → Literal P → Type u where
  | here (l : Literal P) : PurePort o (.lit l) l
  | left {A : NormalForm P} (B : NormalForm P) {l : Literal P} :
      PurePort o A l → PurePort o (o.formula A B) l
  | right (A : NormalForm P) {B : NormalForm P} {l : Literal P} :
      PurePort o B l → PurePort o (o.formula A B) l

namespace PurePort

@[reducible] def positionConj {A : NormalForm P} {l : Literal P} (a : PurePort .conj A l) : A.formula.Occ :=
  match a with
  | .here l => l.point
  | .left _ a => Sum.inl (positionConj a)
  | .right _ a => Sum.inr (positionConj a)
termination_by structural a

@[reducible] def positionDisj {A : NormalForm P} {l : Literal P} (a : PurePort .disj A l) : A.formula.Occ :=
  match a with
  | .here l => l.point
  | .left _ a => Sum.inl (positionDisj a)
  | .right _ a => Sum.inr (positionDisj a)
termination_by structural a

def position {o : Op} {A : NormalForm P} {l : Literal P}
    (a : PurePort o A l) : A.formula.Occ :=
  match o with
  | .conj => positionConj a
  | .disj => positionDisj a

theorem literal {o : Op} {A : NormalForm P} {l : Literal P}
    (a : PurePort o A l) : A.literalAt a.position = l := by
  induction a with
  | here => rfl
  | left B a ih => cases o <;> simpa only [position,NormalForm.literalAt] using ih
  | right A a ih => cases o <;> simpa only [position,NormalForm.literalAt] using ih

/-- Components in the product category and, separately, its coproduct opposite. -/
def arrow {o : Op} {A : NormalForm P} {l : Literal P} :
    PurePort o A l → (side P o).Hom A (.lit l)
  | .here l => (side P o).id (.lit l)
  | .left B a => (side P o).comp ((sideD P o).fst _ B) a.arrow
  | .right A a => (side P o).comp ((sideD P o).snd A _) a.arrow

end PurePort
end DosenPetric.Reduced.Gentzen
