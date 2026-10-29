module

public import DosenPetric.SemanticTransport

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.PresentationSemantics.Interpretation
universe u v w
variable {X : Type u} {C : Category.{u,v} X} {O : Objects X}
  {S : Primitives C O} {P : Type w}

def valuation (F : Interpretation S P) (p : P) : X := F.obj (.var p)

theorem object_evaluation (F : Interpretation S P) (A : Formula P) :
    F.obj A = formula O F.valuation A := by
  induction A with
  | var p => rfl
  | top =>
    exact F.obj_top
  | bot =>
    exact F.obj_bot
  | conj A B ih ih' =>
    exact (F.obj_conj A B).trans (congrArgTwo O.conj ih ih')
  | disj A B ih ih' =>
    exact (F.obj_disj A B).trans (congrArgTwo O.disj ih ih')
  | neg A ih =>
    exact (F.obj_neg A).trans (congrArg O.neg ih)

/-- A full interpretation evaluates every raw term exactly, at the proved object
identifications. This is derived from the primitive laws, not a record field. -/
theorem raw_evaluation (F : Interpretation S P) {A B : Formula P} (t : Presentation.Term P A B) :
    HEq (F.map (Presentation.ofTerm t)) (S.evaluate F.valuation t) := by
  induction t with
  | id A =>
    exact (heq_of_eq (F.toFunctor.map_id A)).trans (heq_apply C.id (F.object_evaluation A))
  | @comp A B D f g ih ih' =>
    exact (heq_of_eq (F.toFunctor.map_comp (Presentation.ofTerm f) (Presentation.ofTerm g))).trans
      (comp_heq (C:=C) (F.object_evaluation A) (F.object_evaluation B) (F.object_evaluation D) ih ih')
  | @tensor o A B D E f g ih ih' =>
    cases o with
    | conj =>
      exact (F.map_tensor .conj (Presentation.ofTerm f) (Presentation.ofTerm g)).trans
        (tensor_heq S .conj (F.object_evaluation A) (F.object_evaluation B)
          (F.object_evaluation D) (F.object_evaluation E) ih ih')
    | disj =>
      exact (F.map_tensor .disj (Presentation.ofTerm f) (Presentation.ofTerm g)).trans
        (tensor_heq S .disj (F.object_evaluation A) (F.object_evaluation B)
          (F.object_evaluation D) (F.object_evaluation E) ih ih')
  | assocR o A B D =>
    cases o with
    | conj =>
      exact (F.map_assocR .conj A B D).trans
        (heq_apply_three (S.assocR .conj) (F.object_evaluation A) (F.object_evaluation B) (F.object_evaluation D))
    | disj =>
      exact (F.map_assocR .disj A B D).trans
        (heq_apply_three (S.assocR .disj) (F.object_evaluation A) (F.object_evaluation B) (F.object_evaluation D))
  | assocL o A B D =>
    cases o with
    | conj =>
      exact (F.map_assocL .conj A B D).trans
        (heq_apply_three (S.assocL .conj) (F.object_evaluation A) (F.object_evaluation B) (F.object_evaluation D))
    | disj =>
      exact (F.map_assocL .disj A B D).trans
        (heq_apply_three (S.assocL .disj) (F.object_evaluation A) (F.object_evaluation B) (F.object_evaluation D))
  | swap o A B =>
    cases o with
    | conj =>
      exact (F.map_swap .conj A B).trans
        (heq_apply_two (S.swap .conj) (F.object_evaluation A) (F.object_evaluation B))
    | disj =>
      exact (F.map_swap .disj A B).trans
        (heq_apply_two (S.swap .disj) (F.object_evaluation A) (F.object_evaluation B))
  | diag A =>
    exact (F.map_diag A).trans (heq_apply S.diag (F.object_evaluation A))
  | codiag A =>
    exact (F.map_codiag A).trans (heq_apply S.codiag (F.object_evaluation A))
  | fst A B =>
    exact (F.map_fst A B).trans
      (heq_apply_two S.fst (F.object_evaluation A) (F.object_evaluation B))
  | snd A B =>
    exact (F.map_snd A B).trans
      (heq_apply_two S.snd (F.object_evaluation A) (F.object_evaluation B))
  | inl A B =>
    exact (F.map_inl A B).trans
      (heq_apply_two S.inl (F.object_evaluation A) (F.object_evaluation B))
  | inr A B =>
    exact (F.map_inr A B).trans
      (heq_apply_two S.inr (F.object_evaluation A) (F.object_evaluation B))
  | rightOut o A =>
    cases o with
    | conj =>
      exact (F.map_rightOut .conj A).trans (heq_apply (S.rightOut .conj) (F.object_evaluation A))
    | disj =>
      exact (F.map_rightOut .disj A).trans (heq_apply (S.rightOut .disj) (F.object_evaluation A))
  | rightIn o A =>
    cases o with
    | conj =>
      exact (F.map_rightIn .conj A).trans (heq_apply (S.rightIn .conj) (F.object_evaluation A))
    | disj =>
      exact (F.map_rightIn .disj A).trans (heq_apply (S.rightIn .disj) (F.object_evaluation A))
  | leftOut o A =>
    cases o with
    | conj =>
      exact (F.map_leftOut .conj A).trans (heq_apply (S.leftOut .conj) (F.object_evaluation A))
    | disj =>
      exact (F.map_leftOut .disj A).trans (heq_apply (S.leftOut .disj) (F.object_evaluation A))
  | leftIn o A =>
    cases o with
    | conj =>
      exact (F.map_leftIn .conj A).trans (heq_apply (S.leftIn .conj) (F.object_evaluation A))
    | disj =>
      exact (F.map_leftIn .disj A).trans (heq_apply (S.leftIn .disj) (F.object_evaluation A))
  | mix A B =>
    exact (F.map_mix A B).trans
      (heq_apply_two S.mix (F.object_evaluation A) (F.object_evaluation B))
  | dist A B D =>
    exact (F.map_dist A B D).trans
      (heq_apply_three S.dist (F.object_evaluation A) (F.object_evaluation B) (F.object_evaluation D))
  | zero A =>
    exact (F.map_zero A).trans (heq_apply S.zero (F.object_evaluation A))
  | dnOut A =>
    exact (F.map_dnOut A).trans (heq_apply S.dnOut (F.object_evaluation A))
  | dnIn A =>
    exact (F.map_dnIn A).trans (heq_apply S.dnIn (F.object_evaluation A))
  | dmConjOut A B =>
    exact (F.map_dmConjOut A B).trans
      (heq_apply_two S.dmConjOut (F.object_evaluation A) (F.object_evaluation B))
  | dmConjIn A B =>
    exact (F.map_dmConjIn A B).trans
      (heq_apply_two S.dmConjIn (F.object_evaluation A) (F.object_evaluation B))
  | dmDisjOut A B =>
    exact (F.map_dmDisjOut A B).trans
      (heq_apply_two S.dmDisjOut (F.object_evaluation A) (F.object_evaluation B))
  | dmDisjIn A B =>
    exact (F.map_dmDisjIn A B).trans
      (heq_apply_two S.dmDisjIn (F.object_evaluation A) (F.object_evaluation B))
  | negTopOut =>
    exact F.map_negTopOut
  | negTopIn =>
    exact F.map_negTopIn
  | negBotOut =>
    exact F.map_negBotOut
  | negBotIn =>
    exact F.map_negBotIn
  | excludedMiddle A =>
    exact (F.map_excludedMiddle A).trans (heq_apply S.excludedMiddle (F.object_evaluation A))
  | contradiction A =>
    exact (F.map_contradiction A).trans (heq_apply S.contradiction (F.object_evaluation A))

theorem hom_evaluation (F : Interpretation S P) (law : S.SatisfiesTheory P)
    {A B : Formula P} (f : Presentation.Hom A B) :
    HEq (F.map f) (S.evaluateHom law F.valuation f) := by
  induction f using Quotient.inductionOn with
  | h t =>
    exact F.raw_evaluation t

end DosenPetric.PresentationSemantics.Interpretation
