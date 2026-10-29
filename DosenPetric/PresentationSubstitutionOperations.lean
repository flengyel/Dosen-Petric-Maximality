module

public import DosenPetric.PresentationSubstitutionRelation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation
universe u v
variable {P : Type u} {R : Type v}

/-- Uniform substitution commutes with the actual derived contravariant negation. -/
theorem substitute_negate (σ : P → Formula R) {A B : Formula P} (f : Hom A B) :
    substitute σ (negate f) = negate (substitute σ f) := by
  apply coherence
  funext y x
  apply propext
  have hn := occurrence_substitute_expanded σ (negate f) y x
  have hf := occurrence_substitute_expanded σ f x y
  have he : occurrenceMap (negate f) = (fun y x => occurrenceMap f x y) := by
    funext y x
    exact propext (occurrence_negate f x y)
  rw [he] at hn
  exact hn.trans ((Relations.Fiber.lift_converse (fun p => (σ p).Occ) A.label B.label
    (occurrenceMap f) (A.expand σ x) (B.expand σ y)).trans
      (hf.symm.trans (occurrence_negate (substitute σ f) x y).symm))

/-- The corresponding admissible equation on the raw primitive grammar. -/
theorem negate_subst_derives (σ : P → Formula R) {A B : Formula P} (t : Term P A B) :
    Derives ((t.negate).subst σ) ((t.subst σ).negate) := by
  apply (ofTerm_eq_iff _ _).mp
  calc
    ofTerm ((t.negate).subst σ) = substitute σ (negate (ofTerm t)) :=
      congrArg (fun f : Hom (.neg B) (.neg A) => substitute σ f) (negateTerm_denotes t)
    _ = negate (substitute σ (ofTerm t)) := substitute_negate σ _
    _ = ofTerm ((t.subst σ).negate) := (negateTerm_denotes (t.subst σ)).symm

def substitutionFunctor (σ : P → Formula R) : Functor (category P) (category R) where
  obj A := A.subst σ
  map := substitute σ
  map_id := substitute_id σ
  map_comp := substitute_comp σ

theorem substitute_tensor_conj (σ : P → Formula R) {A B C D : Formula P}
    (f : Hom A C) (g : Hom B D) :
    substitute σ (tensor .conj f g) = tensor .conj (substitute σ f) (substitute σ g) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

theorem substitute_tensor_disj (σ : P → Formula R) {A B C D : Formula P}
    (f : Hom A C) (g : Hom B D) :
    substitute σ (tensor .disj f g) = tensor .disj (substitute σ f) (substitute σ g) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

theorem substitute_pair (σ : P → Formula R) {X A B : Formula P} (f : Hom X A) (g : Hom X B) :
    substitute σ (pair f g) = pair (substitute σ f) (substitute σ g) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

theorem substitute_copair (σ : P → Formula R) {A B X : Formula P} (f : Hom A X) (g : Hom B X) :
    substitute σ (copair f g) = copair (substitute σ f) (substitute σ g) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

theorem substitute_zeroConstruction (σ : P → Formula R) (A : Formula P) :
    substitute σ (zeroConstruction A) = zeroConstruction (A.subst σ) := rfl

theorem substitute_zeroOf (σ : P → Formula R) {A B : Formula P} (f : Hom A B) :
    substitute σ ((zeroIdentity P).zeroOf f) = (zeroIdentity R).zeroOf (substitute σ f) := by
  change substitute σ (comp (zeroConstruction A) f) = comp (zeroConstruction (A.subst σ)) (substitute σ f)
  rw [substitute_comp,substitute_zeroConstruction]

end DosenPetric.Presentation
