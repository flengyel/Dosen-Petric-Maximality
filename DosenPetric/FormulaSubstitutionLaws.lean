module

public import DosenPetric.OriginalIsolation

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Formula
universe u v w
variable {P : Type u} {R : Type v} {T : Type w}

theorem subst_identity (A : Formula P) : A.subst Formula.var = A := by
  induction A with
  | var p => rfl
  | top => rfl
  | bot => rfl
  | conj A B ih ih' => exact congrArgTwo Formula.conj ih ih'
  | disj A B ih ih' => exact congrArgTwo Formula.disj ih ih'
  | neg A ih => exact congrArg Formula.neg ih

theorem subst_composition (σ : P → Formula R) (τ : R → Formula T) (A : Formula P) :
    (A.subst σ).subst τ = A.subst (fun p => (σ p).subst τ) := by
  induction A with
  | var p => rfl
  | top => rfl
  | bot => rfl
  | conj A B ih ih' => exact congrArgTwo Formula.conj ih ih'
  | disj A B ih ih' => exact congrArgTwo Formula.disj ih ih'
  | neg A ih => exact congrArg Formula.neg ih

theorem subst_ext (σ τ : P → Formula R) (h : ∀ p, σ p = τ p) (A : Formula P) :
    A.subst σ = A.subst τ := by
  have he : σ = τ := funext h
  cases he
  rfl

end DosenPetric.Formula
