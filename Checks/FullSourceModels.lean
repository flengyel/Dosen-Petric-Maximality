module
import DosenPetric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w w'
open DosenPetric
open PresentationSemantics
namespace FullSourceModelChecks
variable {X : Type u} {C : Category.{u,v} X} {O : Objects X} {S : Primitives C O}
  {P : Type w} {R : Type w'}
example (M : Model P S) (α : P → X) : Interpretation S P := S.canonicalInterpretation M.equations α
example (F : Interpretation S R) (σ : P → Formula R) : Interpretation S P := F.precompose σ
example (F : Interpretation S P) (M : Model P S) {A B : Formula P} (f : Presentation.Hom A B) :
    HEq (F.map f) (S.evaluateHom M.equations F.valuation f) := F.hom_evaluation M.equations f
example : Model P (Source.primitives R) := Source.model P R
example : Model Nat (Source.primitives Nat) := Source.model Nat Nat
example : Model Empty (Source.primitives Empty) := Source.model Empty Empty
example : ¬ Nonempty ((Presentation.category Nat).Hom .top .bot) := Presentation.empty_hom Nat
example : Presentation.id (.var 0 : Formula Nat) ≠ Presentation.zero (.var 0) := Presentation.identity_ne_primitive_zero 0
example : Presentation.ProofCongruence P := Agreement.congruence (S:=S) (P:=P)
example : (Agreement.congruence (S:=S) (P:=P)).Closed := Agreement.closed
example (M : Model P S) {A B : Formula P} (f g : Presentation.Hom A B) :
    Agreement S P f g ↔ ∀ α : P → X, S.evaluateHom M.equations α f = S.evaluateHom M.equations α g :=
  Agreement.iff_valuations M.equations f g
example [Nonempty P] (M : Model P S) {A B : Formula P} (f g : Presentation.Hom A B) (hne : f ≠ g)
    (h : ∀ α : P → X, S.evaluateHom M.equations α f = S.evaluateHom M.equations α g) :
    ∀ {Y Z : X} (a b : C.Hom Y Z), a = b := model_corollary M f g hne h
example [Nonempty P] (M : Model P S) {A B : Formula P} (f g : Presentation.Hom A B) (hne : f ≠ g)
    (h : Agreement S P f g) : ∀ {Y Z : X} (a b : C.Hom Y Z), a = b :=
  model_corollary_interpretations M f g hne h
end FullSourceModelChecks

#print axioms DosenPetric.PresentationSemantics.Primitives.evaluate_derives

#print axioms DosenPetric.PresentationSemantics.Primitives.evaluateHom

#print axioms DosenPetric.PresentationSemantics.Primitives.evaluationFunctor

#print axioms DosenPetric.PresentationSemantics.Primitives.canonicalInterpretation

#print axioms DosenPetric.PresentationSemantics.Interpretation.precompose

#print axioms DosenPetric.PresentationSemantics.Interpretation.object_evaluation

#print axioms DosenPetric.PresentationSemantics.Interpretation.raw_evaluation

#print axioms DosenPetric.PresentationSemantics.Interpretation.hom_evaluation

#print axioms DosenPetric.PresentationSemantics.Source.equations

#print axioms DosenPetric.PresentationSemantics.Source.bicartesian

#print axioms DosenPetric.PresentationSemantics.Source.model

#print axioms DosenPetric.PresentationSemantics.Agreement.fragment_closed

#print axioms DosenPetric.PresentationSemantics.Agreement.congruence

#print axioms DosenPetric.PresentationSemantics.Agreement.closed

#print axioms DosenPetric.PresentationSemantics.Agreement.iff_valuations

#print axioms DosenPetric.PresentationSemantics.model_corollary

#print axioms DosenPetric.PresentationSemantics.model_corollary_interpretations

#print axioms DosenPetric.Presentation.fragment_maximality

#print axioms DosenPetric.Presentation.fragment_dichotomy

#print axioms DosenPetric.Presentation.ProofCongruence.of_closed_fragment
