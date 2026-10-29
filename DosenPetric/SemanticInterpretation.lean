module

public import DosenPetric.SemanticQuotientEvaluation

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.PresentationSemantics
universe u v w
variable {X : Type u} {C : Category.{u,v} X} {O : Objects X}

/-- A full-signature interpretation. Heterogeneous equalities retain the
explicit object-operation identifications instead of imposing strict object maps. -/
structure Interpretation (S : Primitives C O) (P : Type w)
    extends Functor (Presentation.category P) C where
  obj_top : toFunctor.obj .top = O.top
  obj_bot : toFunctor.obj .bot = O.bot
  obj_conj : ∀ A B, toFunctor.obj (.conj A B) = O.conj (toFunctor.obj A) (toFunctor.obj B)
  obj_disj : ∀ A B, toFunctor.obj (.disj A B) = O.disj (toFunctor.obj A) (toFunctor.obj B)
  obj_neg : ∀ A, toFunctor.obj (.neg A) = O.neg (toFunctor.obj A)
  map_tensor : ∀ o {A B D E : Formula P} (f : Presentation.Hom A D) (g : Presentation.Hom B E),
    HEq (toFunctor.map (Presentation.tensor o f g))
      (S.tensor o (A:=toFunctor.obj A) (B:=toFunctor.obj B) (D:=toFunctor.obj D) (E:=toFunctor.obj E)
        (toFunctor.map f) (toFunctor.map g))
  map_assocR : ∀ o A B D, HEq (toFunctor.map (Presentation.assocR o A B D))
    (S.assocR o (toFunctor.obj A) (toFunctor.obj B) (toFunctor.obj D))
  map_assocL : ∀ o A B D, HEq (toFunctor.map (Presentation.assocL o A B D))
    (S.assocL o (toFunctor.obj A) (toFunctor.obj B) (toFunctor.obj D))
  map_swap : ∀ o A B, HEq (toFunctor.map (Presentation.swap o A B)) (S.swap o (toFunctor.obj A) (toFunctor.obj B))
  map_diag : ∀ A, HEq (toFunctor.map (Presentation.diag A)) (S.diag (toFunctor.obj A))
  map_codiag : ∀ A, HEq (toFunctor.map (Presentation.codiag A)) (S.codiag (toFunctor.obj A))
  map_fst : ∀ A B, HEq (toFunctor.map (Presentation.fst A B)) (S.fst (toFunctor.obj A) (toFunctor.obj B))
  map_snd : ∀ A B, HEq (toFunctor.map (Presentation.snd A B)) (S.snd (toFunctor.obj A) (toFunctor.obj B))
  map_inl : ∀ A B, HEq (toFunctor.map (Presentation.inl A B)) (S.inl (toFunctor.obj A) (toFunctor.obj B))
  map_inr : ∀ A B, HEq (toFunctor.map (Presentation.inr A B)) (S.inr (toFunctor.obj A) (toFunctor.obj B))
  map_rightOut : ∀ o A, HEq (toFunctor.map (Presentation.rightOut o A)) (S.rightOut o (toFunctor.obj A))
  map_rightIn : ∀ o A, HEq (toFunctor.map (Presentation.rightIn o A)) (S.rightIn o (toFunctor.obj A))
  map_leftOut : ∀ o A, HEq (toFunctor.map (Presentation.leftOut o A)) (S.leftOut o (toFunctor.obj A))
  map_leftIn : ∀ o A, HEq (toFunctor.map (Presentation.leftIn o A)) (S.leftIn o (toFunctor.obj A))
  map_mix : ∀ A B, HEq (toFunctor.map (Presentation.mix A B)) (S.mix (toFunctor.obj A) (toFunctor.obj B))
  map_dist : ∀ A B D, HEq (toFunctor.map (Presentation.dist A B D))
    (S.dist (toFunctor.obj A) (toFunctor.obj B) (toFunctor.obj D))
  map_zero : ∀ A, HEq (toFunctor.map (Presentation.zero A)) (S.zero (toFunctor.obj A))
  map_dnOut : ∀ A, HEq (toFunctor.map (Presentation.dnOut A)) (S.dnOut (toFunctor.obj A))
  map_dnIn : ∀ A, HEq (toFunctor.map (Presentation.dnIn A)) (S.dnIn (toFunctor.obj A))
  map_dmConjOut : ∀ A B, HEq (toFunctor.map (Presentation.dmConjOut A B)) (S.dmConjOut (toFunctor.obj A) (toFunctor.obj B))
  map_dmConjIn : ∀ A B, HEq (toFunctor.map (Presentation.dmConjIn A B)) (S.dmConjIn (toFunctor.obj A) (toFunctor.obj B))
  map_dmDisjOut : ∀ A B, HEq (toFunctor.map (Presentation.dmDisjOut A B)) (S.dmDisjOut (toFunctor.obj A) (toFunctor.obj B))
  map_dmDisjIn : ∀ A B, HEq (toFunctor.map (Presentation.dmDisjIn A B)) (S.dmDisjIn (toFunctor.obj A) (toFunctor.obj B))
  map_negTopOut : HEq (toFunctor.map Presentation.negTopOut) S.negTopOut
  map_negTopIn : HEq (toFunctor.map Presentation.negTopIn) S.negTopIn
  map_negBotOut : HEq (toFunctor.map Presentation.negBotOut) S.negBotOut
  map_negBotIn : HEq (toFunctor.map Presentation.negBotIn) S.negBotIn
  map_excludedMiddle : ∀ A, HEq (toFunctor.map (Presentation.excludedMiddle A)) (S.excludedMiddle (toFunctor.obj A))
  map_contradiction : ∀ A, HEq (toFunctor.map (Presentation.contradiction A)) (S.contradiction (toFunctor.obj A))

namespace Primitives
variable {P : Type w} (S : Primitives C O)

/-- Every variable valuation extends to a constructed full-signature interpretation. -/
def canonicalInterpretation (law : S.SatisfiesTheory P) (α : P → X) : Interpretation S P where
  toFunctor := S.evaluationFunctor law α
  obj_top := rfl
  obj_bot := rfl
  obj_conj _ _ := rfl
  obj_disj _ _ := rfl
  obj_neg _ := rfl
  map_tensor o {A B D E} f g := by
    cases o <;> induction f using Quotient.inductionOn with | h f =>
    all_goals induction g using Quotient.inductionOn with | h g => rfl
  map_assocR o _ _ _ := by cases o <;> rfl
  map_assocL o _ _ _ := by cases o <;> rfl
  map_swap o _ _ := by cases o <;> rfl
  map_diag _ := HEq.rfl
  map_codiag _ := HEq.rfl
  map_fst _ _ := HEq.rfl
  map_snd _ _ := HEq.rfl
  map_inl _ _ := HEq.rfl
  map_inr _ _ := HEq.rfl
  map_rightOut o _ := by cases o <;> rfl
  map_rightIn o _ := by cases o <;> rfl
  map_leftOut o _ := by cases o <;> rfl
  map_leftIn o _ := by cases o <;> rfl
  map_mix _ _ := HEq.rfl
  map_dist _ _ _ := HEq.rfl
  map_zero _ := HEq.rfl
  map_dnOut _ := HEq.rfl
  map_dnIn _ := HEq.rfl
  map_dmConjOut _ _ := HEq.rfl
  map_dmConjIn _ _ := HEq.rfl
  map_dmDisjOut _ _ := HEq.rfl
  map_dmDisjIn _ _ := HEq.rfl
  map_negTopOut := HEq.rfl
  map_negTopIn := HEq.rfl
  map_negBotOut := HEq.rfl
  map_negBotIn := HEq.rfl
  map_excludedMiddle _ := HEq.rfl
  map_contradiction _ := HEq.rfl

end Primitives
end DosenPetric.PresentationSemantics
