module

public import DosenPetric.SubstitutionFiberRelations

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Formula
universe u v
variable {P : Type u} {R : Type v}

theorem contract_injective (σ : P → Formula R) (A : Formula P) {x y : A.Block σ}
    (h : A.contract σ x = A.contract σ y) : x = y := by
  have he := congrArg (A.expand σ) h
  simpa only [expand_contract] using he

theorem contract_eq_iff (σ : P → Formula R) (A : Formula P) (x y : A.Block σ) :
    A.contract σ x = A.contract σ y ↔ x = y :=
  ⟨contract_injective σ A,fun h => congrArg (A.contract σ) h⟩

/-- The occurrence-block bijection commutes with the actual substituted label. -/
theorem contract_label (σ : P → Formula R) (A : Formula P) (x : A.Block σ) :
    (A.subst σ).label (A.contract σ x) = (σ (A.label x.1)).label x.2 := by
  induction A with
  | var p => cases x with | mk x a => cases x; rfl
  | top => exact Empty.elim x.1
  | bot => exact Empty.elim x.1
  | conj A B ih ih' =>
    cases x with
    | mk x a => cases x with | inl x => exact ih ⟨x,a⟩ | inr x => exact ih' ⟨x,a⟩
  | disj A B ih ih' =>
    cases x with
    | mk x a => cases x with | inl x => exact ih ⟨x,a⟩ | inr x => exact ih' ⟨x,a⟩
  | neg A ih => exact ih x

theorem expand_label (σ : P → Formula R) (A : Formula P) (x : (A.subst σ).Occ) :
    (A.subst σ).label x = (σ (A.label (A.expand σ x).1)).label (A.expand σ x).2 := by
  have h := contract_label σ A (A.expand σ x)
  rw [contract_expand] at h
  exact h

/-- Identity relations lift to identity at the exact substituted occurrences. -/
theorem fiber_identity (σ : P → Formula R) (A : Formula P) (x y : A.Block σ) :
    Relations.Fiber.lift (fun p => (σ p).Occ) A.label A.label (Relations.graph _root_.id) x y ↔
      A.contract σ x = A.contract σ y :=
  (Relations.Fiber.lift_identity (fun p => (σ p).Occ) A.label x y).trans (contract_eq_iff σ A x y).symm

end DosenPetric.Formula
