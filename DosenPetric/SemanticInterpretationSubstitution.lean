module

public import DosenPetric.SemanticInterpretation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.PresentationSemantics.Interpretation
universe u v w w'
variable {X : Type u} {C : Category.{u,v} X} {O : Objects X}
  {S : Primitives C O} {P : Type w} {R : Type w'}

/-- Composing a full interpretation with whole-arrow substitution gives another
full interpretation, including its actual object and primitive-arrow laws. -/
def precompose (σ : P → Formula R) (F : Interpretation S R) : Interpretation S P where
  toFunctor := (Presentation.substitutionFunctor σ).comp F.toFunctor
  obj_top := F.obj_top
  obj_bot := F.obj_bot
  obj_conj A B := F.obj_conj (A.subst σ) (B.subst σ)
  obj_disj A B := F.obj_disj (A.subst σ) (B.subst σ)
  obj_neg A := F.obj_neg (A.subst σ)
  map_tensor o {A B D E} f g := by
    cases o with
    | conj =>
      change HEq (F.map (Presentation.substitute σ (Presentation.tensor .conj f g)))
        (S.tensor .conj (F.map (Presentation.substitute σ f)) (F.map (Presentation.substitute σ g)))
      rw [Presentation.substitute_tensor_conj]
      exact F.map_tensor .conj _ _
    | disj =>
      change HEq (F.map (Presentation.substitute σ (Presentation.tensor .disj f g)))
        (S.tensor .disj (F.map (Presentation.substitute σ f)) (F.map (Presentation.substitute σ g)))
      rw [Presentation.substitute_tensor_disj]
      exact F.map_tensor .disj _ _
  map_assocR o A B D := by
    cases o with
    | conj => exact F.map_assocR .conj (A.subst σ) (B.subst σ) (D.subst σ)
    | disj => exact F.map_assocR .disj (A.subst σ) (B.subst σ) (D.subst σ)
  map_assocL o A B D := by
    cases o with
    | conj => exact F.map_assocL .conj (A.subst σ) (B.subst σ) (D.subst σ)
    | disj => exact F.map_assocL .disj (A.subst σ) (B.subst σ) (D.subst σ)
  map_swap o A B := by
    cases o with
    | conj => exact F.map_swap .conj (A.subst σ) (B.subst σ)
    | disj => exact F.map_swap .disj (A.subst σ) (B.subst σ)
  map_diag A := F.map_diag (A.subst σ)
  map_codiag A := F.map_codiag (A.subst σ)
  map_fst A B := F.map_fst (A.subst σ) (B.subst σ)
  map_snd A B := F.map_snd (A.subst σ) (B.subst σ)
  map_inl A B := F.map_inl (A.subst σ) (B.subst σ)
  map_inr A B := F.map_inr (A.subst σ) (B.subst σ)
  map_rightOut o A := by
    cases o with
    | conj => exact F.map_rightOut .conj (A.subst σ)
    | disj => exact F.map_rightOut .disj (A.subst σ)
  map_rightIn o A := by
    cases o with
    | conj => exact F.map_rightIn .conj (A.subst σ)
    | disj => exact F.map_rightIn .disj (A.subst σ)
  map_leftOut o A := by
    cases o with
    | conj => exact F.map_leftOut .conj (A.subst σ)
    | disj => exact F.map_leftOut .disj (A.subst σ)
  map_leftIn o A := by
    cases o with
    | conj => exact F.map_leftIn .conj (A.subst σ)
    | disj => exact F.map_leftIn .disj (A.subst σ)
  map_mix A B := F.map_mix (A.subst σ) (B.subst σ)
  map_dist A B D := F.map_dist (A.subst σ) (B.subst σ) (D.subst σ)
  map_zero A := F.map_zero (A.subst σ)
  map_dnOut A := F.map_dnOut (A.subst σ)
  map_dnIn A := F.map_dnIn (A.subst σ)
  map_dmConjOut A B := F.map_dmConjOut (A.subst σ) (B.subst σ)
  map_dmConjIn A B := F.map_dmConjIn (A.subst σ) (B.subst σ)
  map_dmDisjOut A B := F.map_dmDisjOut (A.subst σ) (B.subst σ)
  map_dmDisjIn A B := F.map_dmDisjIn (A.subst σ) (B.subst σ)
  map_negTopOut := F.map_negTopOut
  map_negTopIn := F.map_negTopIn
  map_negBotOut := F.map_negBotOut
  map_negBotIn := F.map_negBotIn
  map_excludedMiddle A := F.map_excludedMiddle (A.subst σ)
  map_contradiction A := F.map_contradiction (A.subst σ)

theorem precompose_obj (σ : P → Formula R) (F : Interpretation S R) (A : Formula P) :
    (F.precompose σ).obj A = F.obj (A.subst σ) := rfl

theorem precompose_map (σ : P → Formula R) (F : Interpretation S R)
    {A B : Formula P} (f : Presentation.Hom A B) :
    (F.precompose σ).map f = F.map (Presentation.substitute σ f) := rfl

end DosenPetric.PresentationSemantics.Interpretation
