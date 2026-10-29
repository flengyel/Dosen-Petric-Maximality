module

public import DosenPetric.SemanticTransport

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation.Term
open PresentationSemantics
universe u v w

variable {P : Type u} {R : Type v} {T : Type w}

theorem comp_heq {A B D A' B' D' : Formula T}
    (hA : A = A') (hB : B = B') (hD : D = D')
    {f : Term T A B} {f' : Term T A' B'} {g : Term T B D} {g' : Term T B' D'}
    (hf : HEq f f') (hg : HEq g g') : HEq (Term.comp f g) (Term.comp f' g') := by
  cases hA; cases hB; cases hD
  cases eq_of_heq hf; cases eq_of_heq hg
  rfl

theorem tensor_heq (o : Op) {A B D E A' B' D' E' : Formula T}
    (hA : A = A') (hB : B = B') (hD : D = D') (hE : E = E')
    {f : Term T A D} {f' : Term T A' D'} {g : Term T B E} {g' : Term T B' E'}
    (hf : HEq f f') (hg : HEq g g') : HEq (Term.tensor o f g) (Term.tensor o f' g') := by
  cases hA; cases hB; cases hD; cases hE
  cases eq_of_heq hf; cases eq_of_heq hg
  rfl

/-- Raw substitution identity with both endpoint identifications retained. -/
theorem subst_identity_heq {A B : Formula P} (t : Term P A B) : HEq (t.subst Formula.var) t := by
  induction t with
  | @comp A B D f g ih ih' =>
    exact comp_heq (Formula.subst_identity A) (Formula.subst_identity B) (Formula.subst_identity D) ih ih'
  | @tensor o A B D E f g ih ih' =>
    cases o <;> exact tensor_heq _ (Formula.subst_identity A) (Formula.subst_identity B) (Formula.subst_identity D) (Formula.subst_identity E) ih ih'
  | id A =>
    exact heq_apply (Term.id) (Formula.subst_identity A)
  | assocR o A B D =>
    cases o <;>
    exact heq_apply_three (Term.assocR _) (Formula.subst_identity A) (Formula.subst_identity B) (Formula.subst_identity D)
  | assocL o A B D =>
    cases o <;>
    exact heq_apply_three (Term.assocL _) (Formula.subst_identity A) (Formula.subst_identity B) (Formula.subst_identity D)
  | swap o A B =>
    cases o <;>
    exact heq_apply_two (Term.swap _) (Formula.subst_identity A) (Formula.subst_identity B)
  | diag A =>
    exact heq_apply (Term.diag) (Formula.subst_identity A)
  | codiag A =>
    exact heq_apply (Term.codiag) (Formula.subst_identity A)
  | fst A B =>
    exact heq_apply_two (Term.fst) (Formula.subst_identity A) (Formula.subst_identity B)
  | snd A B =>
    exact heq_apply_two (Term.snd) (Formula.subst_identity A) (Formula.subst_identity B)
  | inl A B =>
    exact heq_apply_two (Term.inl) (Formula.subst_identity A) (Formula.subst_identity B)
  | inr A B =>
    exact heq_apply_two (Term.inr) (Formula.subst_identity A) (Formula.subst_identity B)
  | rightOut o A =>
    cases o <;>
    exact heq_apply (Term.rightOut _) (Formula.subst_identity A)
  | rightIn o A =>
    cases o <;>
    exact heq_apply (Term.rightIn _) (Formula.subst_identity A)
  | leftOut o A =>
    cases o <;>
    exact heq_apply (Term.leftOut _) (Formula.subst_identity A)
  | leftIn o A =>
    cases o <;>
    exact heq_apply (Term.leftIn _) (Formula.subst_identity A)
  | mix A B =>
    exact heq_apply_two (Term.mix) (Formula.subst_identity A) (Formula.subst_identity B)
  | dist A B D =>
    exact heq_apply_three (Term.dist) (Formula.subst_identity A) (Formula.subst_identity B) (Formula.subst_identity D)
  | zero A =>
    exact heq_apply (Term.zero) (Formula.subst_identity A)
  | dnOut A =>
    exact heq_apply (Term.dnOut) (Formula.subst_identity A)
  | dnIn A =>
    exact heq_apply (Term.dnIn) (Formula.subst_identity A)
  | dmConjOut A B =>
    exact heq_apply_two (Term.dmConjOut) (Formula.subst_identity A) (Formula.subst_identity B)
  | dmConjIn A B =>
    exact heq_apply_two (Term.dmConjIn) (Formula.subst_identity A) (Formula.subst_identity B)
  | dmDisjOut A B =>
    exact heq_apply_two (Term.dmDisjOut) (Formula.subst_identity A) (Formula.subst_identity B)
  | dmDisjIn A B =>
    exact heq_apply_two (Term.dmDisjIn) (Formula.subst_identity A) (Formula.subst_identity B)
  | negTopOut  =>
    exact HEq.rfl
  | negTopIn  =>
    exact HEq.rfl
  | negBotOut  =>
    exact HEq.rfl
  | negBotIn  =>
    exact HEq.rfl
  | excludedMiddle A =>
    exact heq_apply (Term.excludedMiddle) (Formula.subst_identity A)
  | contradiction A =>
    exact heq_apply (Term.contradiction) (Formula.subst_identity A)

/-- Raw composition of substitutions with the exact formula-action transports. -/
theorem subst_composition_heq (σ : P → Formula R) (τ : R → Formula T)
    {A B : Formula P} (t : Term P A B) :
    HEq ((t.subst σ).subst τ) (t.subst (fun p => (σ p).subst τ)) := by
  induction t with
  | @comp A B D f g ih ih' =>
    exact comp_heq (Formula.subst_composition σ τ A) (Formula.subst_composition σ τ B) (Formula.subst_composition σ τ D) ih ih'
  | @tensor o A B D E f g ih ih' =>
    cases o <;> exact tensor_heq _ (Formula.subst_composition σ τ A) (Formula.subst_composition σ τ B) (Formula.subst_composition σ τ D) (Formula.subst_composition σ τ E) ih ih'
  | id A =>
    exact heq_apply (Term.id) (Formula.subst_composition σ τ A)
  | assocR o A B D =>
    cases o <;>
    exact heq_apply_three (Term.assocR _) (Formula.subst_composition σ τ A) (Formula.subst_composition σ τ B) (Formula.subst_composition σ τ D)
  | assocL o A B D =>
    cases o <;>
    exact heq_apply_three (Term.assocL _) (Formula.subst_composition σ τ A) (Formula.subst_composition σ τ B) (Formula.subst_composition σ τ D)
  | swap o A B =>
    cases o <;>
    exact heq_apply_two (Term.swap _) (Formula.subst_composition σ τ A) (Formula.subst_composition σ τ B)
  | diag A =>
    exact heq_apply (Term.diag) (Formula.subst_composition σ τ A)
  | codiag A =>
    exact heq_apply (Term.codiag) (Formula.subst_composition σ τ A)
  | fst A B =>
    exact heq_apply_two (Term.fst) (Formula.subst_composition σ τ A) (Formula.subst_composition σ τ B)
  | snd A B =>
    exact heq_apply_two (Term.snd) (Formula.subst_composition σ τ A) (Formula.subst_composition σ τ B)
  | inl A B =>
    exact heq_apply_two (Term.inl) (Formula.subst_composition σ τ A) (Formula.subst_composition σ τ B)
  | inr A B =>
    exact heq_apply_two (Term.inr) (Formula.subst_composition σ τ A) (Formula.subst_composition σ τ B)
  | rightOut o A =>
    cases o <;>
    exact heq_apply (Term.rightOut _) (Formula.subst_composition σ τ A)
  | rightIn o A =>
    cases o <;>
    exact heq_apply (Term.rightIn _) (Formula.subst_composition σ τ A)
  | leftOut o A =>
    cases o <;>
    exact heq_apply (Term.leftOut _) (Formula.subst_composition σ τ A)
  | leftIn o A =>
    cases o <;>
    exact heq_apply (Term.leftIn _) (Formula.subst_composition σ τ A)
  | mix A B =>
    exact heq_apply_two (Term.mix) (Formula.subst_composition σ τ A) (Formula.subst_composition σ τ B)
  | dist A B D =>
    exact heq_apply_three (Term.dist) (Formula.subst_composition σ τ A) (Formula.subst_composition σ τ B) (Formula.subst_composition σ τ D)
  | zero A =>
    exact heq_apply (Term.zero) (Formula.subst_composition σ τ A)
  | dnOut A =>
    exact heq_apply (Term.dnOut) (Formula.subst_composition σ τ A)
  | dnIn A =>
    exact heq_apply (Term.dnIn) (Formula.subst_composition σ τ A)
  | dmConjOut A B =>
    exact heq_apply_two (Term.dmConjOut) (Formula.subst_composition σ τ A) (Formula.subst_composition σ τ B)
  | dmConjIn A B =>
    exact heq_apply_two (Term.dmConjIn) (Formula.subst_composition σ τ A) (Formula.subst_composition σ τ B)
  | dmDisjOut A B =>
    exact heq_apply_two (Term.dmDisjOut) (Formula.subst_composition σ τ A) (Formula.subst_composition σ τ B)
  | dmDisjIn A B =>
    exact heq_apply_two (Term.dmDisjIn) (Formula.subst_composition σ τ A) (Formula.subst_composition σ τ B)
  | negTopOut  =>
    exact HEq.rfl
  | negTopIn  =>
    exact HEq.rfl
  | negBotOut  =>
    exact HEq.rfl
  | negBotIn  =>
    exact HEq.rfl
  | excludedMiddle A =>
    exact heq_apply (Term.excludedMiddle) (Formula.subst_composition σ τ A)
  | contradiction A =>
    exact heq_apply (Term.contradiction) (Formula.subst_composition σ τ A)

end DosenPetric.Presentation.Term
