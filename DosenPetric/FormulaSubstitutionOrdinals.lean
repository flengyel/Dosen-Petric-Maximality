module

public import DosenPetric.FiniteBlockConcatenation
public import DosenPetric.FormulaRenamingCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Formula
open FiniteBlocks
universe u v
variable {P : Type u} {Q : Type v}

def blockSizes (σ : P → Formula Q) (A : Formula P) (r : Fin A.occurrenceCount) : Nat :=
  (σ (A.profile r)).occurrenceCount

theorem blockSizes_conj (σ : P → Formula Q) (A B : Formula P) :
    (conj A B).blockSizes σ = concat (A.blockSizes σ) (B.blockSizes σ) := by
  funext i
  simp only [blockSizes,profile,occurrenceAt,concat]
  cases FiniteBlocks.sumDecode i <;> rfl

theorem blockSizes_disj (σ : P → Formula Q) (A B : Formula P) :
    (disj A B).blockSizes σ = concat (A.blockSizes σ) (B.blockSizes σ) := by
  funext i
  simp only [blockSizes,profile,occurrenceAt,concat]
  cases FiniteBlocks.sumDecode i <;> rfl

theorem substitution_count (σ : P → Formula Q) (A : Formula P) :
    (A.subst σ).occurrenceCount = total (A.blockSizes σ) := by
  induction A with
  | var p => rfl
  | top => rfl
  | bot => rfl
  | conj A B ih ih' =>
    rw [blockSizes_conj,total_concat]
    exact congrArgTwo Nat.add ih ih'
  | disj A B ih ih' =>
    rw [blockSizes_disj,total_concat]
    exact congrArgTwo Nat.add ih ih'
  | neg A ih => exact ih

/-- Actual substituted occurrence positions equal prefix offset plus local index. -/
theorem substitution_index (σ : P → Formula Q) (A : Formula P) (x : A.Block σ) :
    ((A.subst σ).occurrenceIndex (A.contract σ x)).val =
      prefixSum (A.blockSizes σ) (A.occurrenceIndex x.1) +
        ((σ (A.label x.1)).occurrenceIndex x.2).val := by
  induction A with
  | var p =>
    obtain ⟨r,t⟩ := x
    cases r
    change ((σ p).occurrenceIndex t).val = prefixSum ((var p).blockSizes σ) (0 : Fin 1) + ((σ p).occurrenceIndex t).val
    rw [prefixSum_zero,Nat.zero_add]
  | top => exact Empty.elim x.1
  | bot => exact Empty.elim x.1
  | conj A B ih ih' =>
    obtain ⟨r,t⟩ := x
    cases r with
    | inl r =>
      change ((A.subst σ).occurrenceIndex (A.contract σ ⟨r,t⟩)).val =
        prefixSum ((conj A B).blockSizes σ) (sumEncode (.inl (A.occurrenceIndex r))) +
          ((σ (A.label r)).occurrenceIndex t).val
      rw [blockSizes_conj,prefix_concat_left]
      exact ih ⟨r,t⟩
    | inr r =>
      change (A.subst σ).occurrenceCount + ((B.subst σ).occurrenceIndex (B.contract σ ⟨r,t⟩)).val =
        prefixSum ((conj A B).blockSizes σ) (sumEncode (.inr (B.occurrenceIndex r))) +
          ((σ (B.label r)).occurrenceIndex t).val
      rw [blockSizes_conj,prefix_concat_right,substitution_count,ih']
      exact (Nat.add_assoc _ _ _).symm
  | disj A B ih ih' =>
    obtain ⟨r,t⟩ := x
    cases r with
    | inl r =>
      change ((A.subst σ).occurrenceIndex (A.contract σ ⟨r,t⟩)).val =
        prefixSum ((disj A B).blockSizes σ) (sumEncode (.inl (A.occurrenceIndex r))) +
          ((σ (A.label r)).occurrenceIndex t).val
      rw [blockSizes_disj,prefix_concat_left]
      exact ih ⟨r,t⟩
    | inr r =>
      change (A.subst σ).occurrenceCount + ((B.subst σ).occurrenceIndex (B.contract σ ⟨r,t⟩)).val =
        prefixSum ((disj A B).blockSizes σ) (sumEncode (.inr (B.occurrenceIndex r))) +
          ((σ (B.label r)).occurrenceIndex t).val
      rw [blockSizes_disj,prefix_concat_right,substitution_count,ih']
      exact (Nat.add_assoc _ _ _).symm
  | neg A ih => exact ih x

end DosenPetric.Formula
