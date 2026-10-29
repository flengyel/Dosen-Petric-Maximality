module
import DosenPetric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open DosenPetric
namespace FullPaperClaimChecks
open Presentation
example {P : Type u} {A B : Formula P} (f g : Hom A B) (hne : f ≠ g) :
    ∃ (l : Literal P) (i : Hom (.conj l.formula .bot) A) (r : Hom B (.disj l.formula .top)),
      (comp (comp i f) r = comp (fst l.formula .bot) (inl l.formula .top) ∧
       comp (comp i g) r = (zeroIdentity P).zeroOf (comp (fst l.formula .bot) (inl l.formula .top))) ∨
      (comp (comp i g) r = comp (fst l.formula .bot) (inl l.formula .top) ∧
       comp (comp i f) r = (zeroIdentity P).zeroOf (comp (fst l.formula .bot) (inl l.formula .top))) := occurrence_isolation f g hne
example {P : Type u} (A : Formula P) : Subsingleton (Hom .top A) := inferInstance
example {P : Type u} (l : Literal P) : Presentation.id l.formula ≠ zeroConstruction l.formula := literal_identity_ne_zero l
example {P : Type u} (p : P) : Presentation.id (.var p) ≠ zeroConstruction (.var p) := identity_ne_zero p
example {P : Type u} (p : P) : Presentation.id (.var p) ≠ zero (.var p) := identity_ne_primitive_zero p
example {P : Type u} (p : P) : ¬ Nonempty (ExponentialData (operations P) (.conj (.var p) (.var p)) (.var p)) := no_projection_exponential p
example {P : Type u} (p : P) : ¬ (∀ A B : Formula P, Nonempty (ExponentialData (operations P) A B)) := not_cartesian_closed p
example {P : Type u} (A B C : Formula P) :
    comp (ManuscriptDiagrams.firstUpper A B C) (ManuscriptDiagrams.firstRight A B C) =
      ManuscriptDiagrams.firstDiagonal A B C := ManuscriptDiagrams.first_triangle A B C
example {P : Type u} (A : Formula P) : ManuscriptDiagrams.zeroPath A = (zeroIdentity P).zero A := ManuscriptDiagrams.zero_diagram A
example {P : Type u} (A : Formula P) : ManuscriptDiagrams.zeroPath A = zero A := ManuscriptDiagrams.zero_primitive A
example {P : Type u} {A B : Formula P} (f g : Hom A B) :
    comp (ManuscriptDiagrams.zeroPath A) f = comp g (ManuscriptDiagrams.zeroPath B) := ManuscriptDiagrams.zero_square f g
example {P : Type u} (A B : Formula P) : (operations P).fold A B = comp (mix A A) (codiag A) := fold_source_mix A B
example {P : Type u} (A B : Formula P) :
    (operations P).fold A B = comp (mix A A) (copair (Presentation.id A) (Presentation.id A)) := fold_manuscript A B
example {P : Type u} (A B D : Formula P) : (operations P).fold A B = (operations P).fold A D := fold_parameter_independent A B D
example {P : Type u} (A : Formula P) :
    comp (pair (snd A A) (fst A A)) (comp (mix A A) (codiag A)) = comp (mix A A) (codiag A) := fold_symmetric A
section
variable {P : Type u} {R : Type v} (σ : P → Formula R)
example : Functor (category P) (category R) := substitutionFunctor σ
example {A B : Formula P} (t : Term P A B) (x : A.Block σ) (y : B.Block σ) :
    (t.subst σ).relation (A.contract σ x) (B.contract σ y) ↔
      Relations.Fiber.lift (fun p => (σ p).Occ) A.label B.label t.relation x y := t.substitution_coordinates σ x y
example {A B : Formula P} (f : Hom A B) (x : A.Block σ) (y : B.Block σ) :
    occurrenceMap (substitute σ f) (A.contract σ x) (B.contract σ y) ↔
      Relations.Fiber.lift (fun p => (σ p).Occ) A.label B.label (occurrenceMap f) x y := occurrence_substitute_coordinates σ f x y
example {A B : Formula P} (f : Hom A B) : substitute σ (negate f) = negate (substitute σ f) := substitute_negate σ f
example {A B : Formula P} (t : Term P A B) : Derives ((t.negate).subst σ) ((t.subst σ).negate) := negate_subst_derives σ t
example {A B : Formula P} (f : Hom A B) :
    substitute σ ((zeroIdentity P).zeroOf f) = (zeroIdentity R).zeroOf (substitute σ f) := substitute_zeroOf σ f
example (A : Formula P) (x : A.Block σ) :
    (A.subst σ).label (A.contract σ x) = (σ (A.label x.1)).label x.2 := Formula.contract_label σ A x
end
example : ¬ occurrenceMap (substitute (fun _ : Nat => (Formula.conj (.var 0) (.var 0) : Formula Nat))
    (Presentation.id (.var 0))) (Sum.inl ()) (Sum.inr ()) := by
  change ¬ ((Sum.inl () : Sum Unit Unit) = Sum.inr ())
  intro h
  cases h
example : substitute (fun _ : Nat => (Formula.top : Formula Empty)) (Presentation.id (.var 0)) =
    Presentation.id (.top : Formula Empty) := rfl
example : Subsingleton (Hom (.top : Formula Empty) .bot) := inferInstance
example : ¬ Nonempty ((category Empty).Hom .top .bot) := empty_hom Empty
end FullPaperClaimChecks

#print axioms DosenPetric.Presentation.occurrence_isolation

#print axioms DosenPetric.Presentation.literal_identity_ne_zero

#print axioms DosenPetric.Presentation.identity_ne_zero

#print axioms DosenPetric.Presentation.identity_ne_primitive_zero

#print axioms DosenPetric.Presentation.no_projection_exponential

#print axioms DosenPetric.Presentation.not_cartesian_closed

#print axioms DosenPetric.Presentation.fold_source_mix

#print axioms DosenPetric.Presentation.fold_manuscript

#print axioms DosenPetric.Presentation.fold_parameter_independent

#print axioms DosenPetric.Presentation.fold_symmetric

#print axioms DosenPetric.Presentation.occurrence_substitute_coordinates

#print axioms DosenPetric.Presentation.occurrence_substitute_expanded

#print axioms DosenPetric.Presentation.substitute_negate

#print axioms DosenPetric.Presentation.negate_subst_derives

#print axioms DosenPetric.Presentation.substitutionFunctor

#print axioms DosenPetric.Presentation.substitute_zeroOf

#print axioms DosenPetric.Presentation.Term.substitution_coordinates

#print axioms DosenPetric.ExponentialData.hom_unique

#print axioms DosenPetric.Isolation.original_witnesses

#print axioms DosenPetric.Relations.Fiber.lift_composition

#print axioms DosenPetric.Relations.Fiber.lift_graph

#print axioms DosenPetric.Formula.contract_label

#print axioms DosenPetric.Formula.graph_coordinates

#print axioms DosenPetric.Presentation.ManuscriptDiagrams.first_triangle

#print axioms DosenPetric.Presentation.ManuscriptDiagrams.zero_diagram

#print axioms DosenPetric.Presentation.ManuscriptDiagrams.zero_primitive

#print axioms DosenPetric.Presentation.ManuscriptDiagrams.zero_square
