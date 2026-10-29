module

public import DosenPetric.PresentationSubstitutionRemaining

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation.Term
universe u v
variable {P : Type u} {R : Type v}

/-- Every primitive source constructor satisfies the exact substituted block square. -/
theorem substitution_coordinates (σ : P → Formula R) {A B : Formula P} (t : Term P A B) :
    SubstitutionCompatible σ t := by
  induction t with
  | id A => exact substitution_id σ A
  | comp f g ih ih' => exact substitution_comp σ f g ih ih'
  | tensor o f g ih ih' => exact substitution_tensor σ o f g ih ih'
  | assocR o A B C => exact substitution_assocR σ o A B C
  | assocL o A B C => exact substitution_assocL σ o A B C
  | swap o A B => exact substitution_swap σ o A B
  | diag A => exact substitution_diag σ A
  | codiag A => exact substitution_codiag σ A
  | fst A B => exact substitution_fst σ A B
  | snd A B => exact substitution_snd σ A B
  | inl A B => exact substitution_inl σ A B
  | inr A B => exact substitution_inr σ A B
  | rightOut o A => exact substitution_rightOut σ o A
  | rightIn o A => exact substitution_rightIn σ o A
  | leftOut o A => exact substitution_leftOut σ o A
  | leftIn o A => exact substitution_leftIn σ o A
  | mix A B => exact substitution_mix σ A B
  | dist A B C => exact substitution_dist σ A B C
  | zero A => exact substitution_zero σ A
  | dnOut A => exact substitution_dnOut σ A
  | dnIn A => exact substitution_dnIn σ A
  | dmConjOut A B => exact substitution_dmConjOut σ A B
  | dmConjIn A B => exact substitution_dmConjIn σ A B
  | dmDisjOut A B => exact substitution_dmDisjOut σ A B
  | dmDisjIn A B => exact substitution_dmDisjIn σ A B
  | negTopOut => exact substitution_negTopOut σ
  | negTopIn => exact substitution_negTopIn σ
  | negBotOut => exact substitution_negBotOut σ
  | negBotIn => exact substitution_negBotIn σ
  | excludedMiddle A => exact substitution_excludedMiddle σ A
  | contradiction A => exact substitution_contradiction σ A

end DosenPetric.Presentation.Term
namespace DosenPetric.Presentation
universe u v
variable {P : Type u} {R : Type v}

theorem occurrence_substitute_coordinates (σ : P → Formula R) {A B : Formula P} (f : Hom A B)
    (x : A.Block σ) (y : B.Block σ) :
    occurrenceMap (substitute σ f) (A.contract σ x) (B.contract σ y) ↔
      Relations.Fiber.lift (fun p => (σ p).Occ) A.label B.label (occurrenceMap f) x y := by
  induction f using Quotient.inductionOn with
  | h t => exact t.substitution_coordinates σ x y

/-- The whole-arrow block square at arbitrary actual substituted occurrences. -/
theorem occurrence_substitute_expanded (σ : P → Formula R) {A B : Formula P} (f : Hom A B)
    (x : (A.subst σ).Occ) (y : (B.subst σ).Occ) :
    occurrenceMap (substitute σ f) x y ↔
      Relations.Fiber.lift (fun p => (σ p).Occ) A.label B.label (occurrenceMap f)
        (A.expand σ x) (B.expand σ y) := by
  have h := occurrence_substitute_coordinates σ f (A.expand σ x) (B.expand σ y)
  rw [Formula.contract_expand,Formula.contract_expand] at h
  exact h

end DosenPetric.Presentation
