module

public import DosenPetric.SemanticEvaluation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.PresentationSemantics.Primitives
universe u v w
variable {X : Type u} {C : Category.{u,v} X} {O : Objects X}
  {P : Type w} (S : Primitives C O)

theorem evaluate_derives (law : S.SatisfiesTheory P) (α : P → X)
    {A B : Formula P} {f g : Presentation.Term P A B} (h : Presentation.Derives f g) :
    S.evaluate α f = S.evaluate α g := by
  induction h with
  | refl f => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | equation h => exact law α h
  | comp _ _ ih ih' => exact congrArgTwo C.comp ih ih'
  | tensor o _ _ ih ih' => cases o <;> exact congrArgTwo (S.tensor _) ih ih'

/-- Actual descent from the complete source syntax to the equation-generated quotient. -/
def evaluateHom (law : S.SatisfiesTheory P) (α : P → X) {A B : Formula P}
    (f : Presentation.Hom A B) : C.Hom (formula O α A) (formula O α B) :=
  Quotient.liftOn f (fun t => S.evaluate α t) (fun _ _ h => S.evaluate_derives law α h)

theorem evaluateHom_ofTerm (law : S.SatisfiesTheory P) (α : P → X)
    {A B : Formula P} (t : Presentation.Term P A B) :
    S.evaluateHom law α (Presentation.ofTerm t) = S.evaluate α t := rfl

theorem evaluateHom_id (law : S.SatisfiesTheory P) (α : P → X) (A : Formula P) :
    S.evaluateHom law α (Presentation.id A) = C.id (formula O α A) := rfl

theorem evaluateHom_comp (law : S.SatisfiesTheory P) (α : P → X)
    {A B D : Formula P} (f : Presentation.Hom A B) (g : Presentation.Hom B D) :
    S.evaluateHom law α (Presentation.comp f g) =
      C.comp (S.evaluateHom law α f) (S.evaluateHom law α g) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

/-- Every valuation has a constructed quotient functor. -/
def evaluationFunctor (law : S.SatisfiesTheory P) (α : P → X) :
    Functor (Presentation.category P) C where
  obj := formula O α
  map := S.evaluateHom law α
  map_id := S.evaluateHom_id law α
  map_comp := S.evaluateHom_comp law α

end DosenPetric.PresentationSemantics.Primitives
