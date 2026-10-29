module

public import DosenPetric.GentzenPurePorts

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.PurePort
universe u
variable {P : Type u}

/-- Pure formulas have exactly the signed literal ports carried by their positions. -/
def ofPosition (o : Op) (A : NormalForm P) (h : Pure o A) (x : A.formula.Occ) :
    PurePort o A (A.literalAt x) :=
  match A with
  | .lit l => .here l
  | .top => nomatch x
  | .bot => nomatch x
  | .conj A B => by
    cases o with
    | conj =>
      cases x with
      | inl x => exact .left B (ofPosition .conj A h.1 x)
      | inr x => exact .right A (ofPosition .conj B h.2 x)
    | disj => exact False.elim h
  | .disj A B => by
    cases o with
    | conj => exact False.elim h
    | disj =>
      cases x with
      | inl x => exact .left B (ofPosition .disj A h.1 x)
      | inr x => exact .right A (ofPosition .disj B h.2 x)

theorem position_ofPosition (o : Op) (A : NormalForm P) (h : Pure o A)
    (x : A.formula.Occ) : (ofPosition o A h x).position = x := by
  induction A with
  | lit l => cases o <;> simpa only [ofPosition,position] using (l.occ_unique x).symm
  | top => cases x
  | bot => cases x
  | conj A B ih ih' =>
    cases o with
    | disj => exact False.elim h
    | conj =>
      cases x with
      | inl x => simpa only [ofPosition,position] using congrArg (Sum.inl (β:=B.formula.Occ)) (ih h.1 x)
      | inr x => simpa only [ofPosition,position] using congrArg (Sum.inr (α:=A.formula.Occ)) (ih' h.2 x)
  | disj A B ih ih' =>
    cases o with
    | conj => exact False.elim h
    | disj =>
      cases x with
      | inl x => simpa only [ofPosition,position] using congrArg (Sum.inl (β:=B.formula.Occ)) (ih h.1 x)
      | inr x => simpa only [ofPosition,position] using congrArg (Sum.inr (α:=A.formula.Occ)) (ih' h.2 x)

theorem position_injective {o : Op} {A : NormalForm P} {l : Literal P}
    (a b : PurePort o A l) (h : a.position = b.position) : a = b := by
  cases o <;> (induction a with
    | here l => cases b; rfl
    | left B a ih =>
      cases b with
      | left B b =>
        simp only [position] at h
        exact congrArg (PurePort.left B) (ih b (Sum.inl.inj h))
      | right A b => simp only [position] at h; cases h
    | right A a ih =>
      cases b with
      | left B b => simp only [position] at h; cases h
      | right A b =>
        simp only [position] at h
        exact congrArg (PurePort.right A) (ih b (Sum.inr.inj h)))

theorem label_of_position_eq {o : Op} {A : NormalForm P} {l m : Literal P}
    (a : PurePort o A l) (b : PurePort o A m) (h : a.position = b.position) : l = m :=
  a.literal.symm.trans ((congrArg A.literalAt h).trans b.literal)

/-- Embed an internal port at its exact whole-formula context tag. -/
def inContext (o : Op) {Γ : List (NormalForm P)} {A : NormalForm P} {l : Literal P}
    (a : At Γ A) (p : PurePort o A l) : PurePort o (fold o Γ) l :=
  match a with
  | .here _ U => .left (fold o U) p
  | .there a => .right _ (inContext o a p)

theorem inContext_arrow (o : Op) {Γ : List (NormalForm P)} {A : NormalForm P} {l : Literal P}
    (a : At Γ A) (p : PurePort o A l) :
    (inContext o a p).arrow = (side P o).comp (component o a) p.arrow := by
  induction a with
  | here => cases o <;> rfl
  | there a ih =>
    rw [inContext,arrow,ih]
    rw [component_there]
    exact ((side P o).assoc ..).symm

end DosenPetric.Reduced.Gentzen.PurePort
