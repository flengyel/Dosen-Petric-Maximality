module

public import DosenPetric.FormulaFiniteOccurrences

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Formula
universe u v w
variable {P : Type u} {Q : Type v} {R : Type w}

def rename (ρ : P → Q) (A : Formula P) : Formula Q := A.subst (fun p => .var (ρ p))

def renameOcc (ρ : P → Q) : (A : Formula P) → A.Occ → (A.rename ρ).Occ
  | .var _,_ => ()
  | .top,x => Empty.elim x
  | .bot,x => Empty.elim x
  | .conj A _,.inl x => .inl (A.renameOcc ρ x)
  | .conj _ B,.inr x => .inr (B.renameOcc ρ x)
  | .disj A _,.inl x => .inl (A.renameOcc ρ x)
  | .disj _ B,.inr x => .inr (B.renameOcc ρ x)
  | .neg A,x => A.renameOcc ρ x

def unrenameOcc (ρ : P → Q) : (A : Formula P) → (A.rename ρ).Occ → A.Occ
  | .var _,_ => ()
  | .top,x => Empty.elim x
  | .bot,x => Empty.elim x
  | .conj A _,.inl x => .inl (A.unrenameOcc ρ x)
  | .conj _ B,.inr x => .inr (B.unrenameOcc ρ x)
  | .disj A _,.inl x => .inl (A.unrenameOcc ρ x)
  | .disj _ B,.inr x => .inr (B.unrenameOcc ρ x)
  | .neg A,x => A.unrenameOcc ρ x

theorem unrename_rename (ρ : P → Q) (A : Formula P) (x : A.Occ) :
    A.unrenameOcc ρ (A.renameOcc ρ x) = x := by
  induction A with
  | var p => cases x; rfl
  | top => exact Empty.elim x
  | bot => exact Empty.elim x
  | conj A B ih ih' | disj A B ih ih' =>
    cases x with
    | inl x => exact congrArg Sum.inl (ih x)
    | inr x => exact congrArg Sum.inr (ih' x)
  | neg A ih => exact ih x

theorem rename_unrename (ρ : P → Q) (A : Formula P) (x : (A.rename ρ).Occ) :
    A.renameOcc ρ (A.unrenameOcc ρ x) = x := by
  induction A with
  | var p => cases x; rfl
  | top => exact Empty.elim x
  | bot => exact Empty.elim x
  | conj A B ih ih' | disj A B ih ih' =>
    cases x with
    | inl x => exact congrArg Sum.inl (ih x)
    | inr x => exact congrArg Sum.inr (ih' x)
  | neg A ih => exact ih x

theorem rename_label (ρ : P → Q) (A : Formula P) (x : A.Occ) :
    (A.rename ρ).label (A.renameOcc ρ x) = ρ (A.label x) := by
  induction A with
  | var p => rfl
  | top => exact Empty.elim x
  | bot => exact Empty.elim x
  | conj A B ih ih' | disj A B ih ih' =>
    cases x with
    | inl x => exact ih x
    | inr x => exact ih' x
  | neg A ih => exact ih x

theorem unrename_label (ρ : P → Q) (A : Formula P) (x : (A.rename ρ).Occ) :
    ρ (A.label (A.unrenameOcc ρ x)) = (A.rename ρ).label x := by
  have he := A.rename_label ρ (A.unrenameOcc ρ x)
  rw [rename_unrename] at he
  exact he.symm

theorem renameOcc_injective (ρ : P → Q) (A : Formula P) {x y : A.Occ}
    (h : A.renameOcc ρ x = A.renameOcc ρ y) : x = y := by
  have he := congrArg (A.unrenameOcc ρ) h
  rw [unrename_rename,unrename_rename] at he
  exact he

theorem rename_count (ρ : P → Q) (A : Formula P) : (A.rename ρ).occurrenceCount = A.occurrenceCount := by
  induction A with
  | var p => rfl
  | top => rfl
  | bot => rfl
  | conj A B ih ih' | disj A B ih ih' => exact congrArgTwo Nat.add ih ih'
  | neg A ih => exact ih

/-- Renaming may identify labels; it never identifies occurrence positions. -/
theorem rename_substitution (σ : P → Formula Q) (ρ : Q → R) (A : Formula P) :
    (A.subst σ).rename ρ = A.subst (fun p => (σ p).rename ρ) :=
  subst_composition σ (fun q => .var (ρ q)) A

end DosenPetric.Formula
