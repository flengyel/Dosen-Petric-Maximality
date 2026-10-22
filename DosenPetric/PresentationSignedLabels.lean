module

public import DosenPetric.PresentationNormalization

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.Presentation

universe u

variable {P : Type u}

/-- Every edge of a primitive arrow term preserves the complete signed label.
The induction is on syntax; neither coherence nor a faithful interpretation is used. -/
theorem Term.relation_signedLabel {A B : Formula P} (t : Term P A B)
    (x : A.Occ) (y : B.Occ) (h : t.relation x y) :
    A.signedLabel x = B.signedLabel y := by
  induction t with
  | id A => cases h; rfl
  | comp f g ih ih' =>
    rcases h with ⟨z, hf, hg⟩
    exact (ih x z hf).trans (ih' z y hg)
  | tensor o f g ih ih' =>
    cases o <;> cases x <;> cases y <;>
      first | exact False.elim h | exact ih _ _ h | exact ih' _ _ h
  | assocR o A B C =>
    cases o <;> cases h <;> rcases x with x | (x | x) <;> rfl
  | assocL o A B C =>
    cases o <;> cases h <;> rcases x with (x | x) | x <;> rfl
  | swap o A B =>
    cases o <;> cases h <;> cases x <;> rfl
  | diag A => cases y <;> cases h <;> rfl
  | codiag A => cases x <;> cases h <;> rfl
  | fst A B =>
    cases x with
    | inl x => cases h; rfl
    | inr _ => exact False.elim h
  | snd A B =>
    cases x with
    | inl _ => exact False.elim h
    | inr x => cases h; rfl
  | inl A B => cases h; rfl
  | inr A B => cases h; rfl
  | rightOut o A =>
    cases o <;> cases x with
    | inl x => cases h; rfl
    | inr e => exact Empty.elim e
  | rightIn o A => cases o <;> cases h <;> rfl
  | leftOut o A =>
    cases o <;> cases x with
    | inl e => exact Empty.elim e
    | inr x => cases h; rfl
  | leftIn o A => cases o <;> cases h <;> rfl
  | mix A B => cases h; cases x <;> rfl
  | dist A B C => cases h; rcases x with x | (x | x) <;> rfl
  | zero A => exact False.elim h
  | dnOut A => cases h; exact Literal.flip_flip _
  | dnIn A => cases h; exact (Literal.flip_flip _).symm
  | dmConjOut A B => cases h; cases x <;> rfl
  | dmConjIn A B => cases h; cases x <;> rfl
  | dmDisjOut A B => cases h; cases x <;> rfl
  | dmDisjIn A B => cases h; cases x <;> rfl
  | negTopOut => exact Empty.elim x
  | negTopIn => exact Empty.elim x
  | negBotOut => exact Empty.elim x
  | negBotIn => exact Empty.elim x
  | excludedMiddle A => exact False.elim h
  | contradiction A => exact False.elim h

/-- Signed-label preservation descends through the already well-defined occurrence map. -/
theorem occurrence_signedLabel {A B : Formula P} (f : Hom A B)
    (x : A.Occ) (y : B.Occ) (h : occurrenceMap f x y) :
    A.signedLabel x = B.signedLabel y := by
  induction f using Quotient.inductionOn with
  | h t =>
    change occurrenceMap (ofTerm t) x y at h
    rw [occurrence_ofTerm] at h
    exact t.relation_signedLabel x y h

theorem occurrence_label {A B : Formula P} (f : Hom A B)
    (x : A.Occ) (y : B.Occ) (h : occurrenceMap f x y) : A.label x = B.label y :=
  (Formula.signedLabel_letter A x).symm.trans
    ((congrArg Literal.letter (occurrence_signedLabel f x y h)).trans
      (Formula.signedLabel_letter B y))

theorem occurrence_polarity {A B : Formula P} (f : Hom A B)
    (x : A.Occ) (y : B.Occ) (h : occurrenceMap f x y) : A.polarity x = B.polarity y :=
  congrArg Literal.negative (occurrence_signedLabel f x y h)

theorem no_edge_of_polarity_ne {A B : Formula P} (f : Hom A B)
    (x : A.Occ) (y : B.Occ) (hne : A.polarity x ≠ B.polarity y) :
    ¬ occurrenceMap f x y := fun h => hne (occurrence_polarity f x y h)

/-- In particular, opposite polarities of the same variable cannot be joined. -/
theorem no_edge_opposite_literals {A B : Formula P} (f : Hom A B)
    (x : A.Occ) (y : B.Occ) (p : P)
    (hx : A.signedLabel x = .pos p) (hy : B.signedLabel y = .neg p) :
    ¬ occurrenceMap f x y := by
  intro h
  have e := occurrence_signedLabel f x y h
  rw [hx, hy] at e
  cases e

theorem no_edge_negative_positive_literals {A B : Formula P} (f : Hom A B)
    (x : A.Occ) (y : B.Occ) (p : P)
    (hx : A.signedLabel x = .neg p) (hy : B.signedLabel y = .pos p) :
    ¬ occurrenceMap f x y := by
  intro h
  have e := occurrence_signedLabel f x y h
  rw [hx, hy] at e
  cases e

/-- On normal forms the invariant is equality of literals, including their signs. -/
theorem occurrence_literal (A B : NormalForm P) (f : Hom A.formula B.formula)
    (x : A.formula.Occ) (y : B.formula.Occ) (h : occurrenceMap f x y) :
    A.literalAt x = B.literalAt y := by
  rw [← NormalForm.signedLabel_eq_literalAt, ← NormalForm.signedLabel_eq_literalAt]
  exact occurrence_signedLabel f x y h

theorem occurrence_literal_letter (A B : NormalForm P) (f : Hom A.formula B.formula)
    (x : A.formula.Occ) (y : B.formula.Occ) (h : occurrenceMap f x y) :
    (A.literalAt x).letter = (B.literalAt y).letter :=
  congrArg Literal.letter (occurrence_literal A B f x y h)

theorem occurrence_literal_polarity (A B : NormalForm P) (f : Hom A.formula B.formula)
    (x : A.formula.Occ) (y : B.formula.Occ) (h : occurrenceMap f x y) :
    (A.literalAt x).negative = (B.literalAt y).negative :=
  congrArg Literal.negative (occurrence_literal A B f x y h)

theorem no_edge_of_literal_ne (A B : NormalForm P) (f : Hom A.formula B.formula)
    (x : A.formula.Occ) (y : B.formula.Occ) (hne : A.literalAt x ≠ B.literalAt y) :
    ¬ occurrenceMap f x y := fun h => hne (occurrence_literal A B f x y h)

/-- Label agreement allows copying into two distinct tagged positions. -/
theorem diag_copies (p : P) :
    occurrenceMap (diag (.var p)) () (.inl ()) ∧
    occurrenceMap (diag (.var p)) () (.inr ()) ∧
    (Sum.inl () : (Formula.conj (.var p) (.var p)).Occ) ≠ .inr () := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  cases h

/-- Label agreement allows merging two distinct tagged positions. -/
theorem codiag_merges (p : P) :
    occurrenceMap (codiag (.var p)) (.inl ()) () ∧
    occurrenceMap (codiag (.var p)) (.inr ()) () ∧
    (Sum.inl () : (Formula.disj (.var p) (.var p)).Occ) ≠ .inr () := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  cases h

namespace NegationNormalization

/-- The transported edge preserves literals in the existing normalizer's coordinates. -/
theorem transport_literal {A B : Formula P} (f : Hom A B)
    (x : (normal A).formula.Occ) (y : (normal B).formula.Occ)
    (h : occurrenceMap ((normalization P).transport f) x y) :
    (normal A).literalAt x = (normal B).literalAt y := by
  have edge := (transport_apply f x y).mp h
  exact (literal_fromOcc A x).symm.trans
    ((occurrence_signedLabel f _ _ edge).trans (literal_fromOcc B y))

theorem transport_literal_coordinates {A B : Formula P} (f : Hom A B)
    (x : A.Occ) (y : B.Occ) (h : occurrenceMap f x y) :
    (normal A).literalAt (toOcc A x) = (normal B).literalAt (toOcc B y) :=
  transport_literal f _ _ ((transport_coordinates f x y).mpr h)

end NegationNormalization

end DosenPetric.Presentation
