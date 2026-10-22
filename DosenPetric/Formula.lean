module

public import Init

@[expose] public section

set_option autoImplicit false

namespace DosenPetric

universe u v

inductive Formula (P : Type u) where
  | var : P → Formula P
  | top : Formula P
  | bot : Formula P
  | conj : Formula P → Formula P → Formula P
  | disj : Formula P → Formula P → Formula P
  | neg : Formula P → Formula P

namespace Formula

variable {P : Type u} {Q : Type v}

/-- Tagged positions distinguish repeated occurrences of a variable. -/
def Occ : Formula P → Type
  | .var _ => Unit
  | .top => Empty
  | .bot => Empty
  | .conj A B => Sum A.Occ B.Occ
  | .disj A B => Sum A.Occ B.Occ
  | .neg A => A.Occ

def label : (A : Formula P) → A.Occ → P
  | .var p, _ => p
  | .top, x => nomatch x
  | .bot, x => nomatch x
  | .conj A _, .inl x => A.label x
  | .conj _ B, .inr x => B.label x
  | .disj A _, .inl x => A.label x
  | .disj _ B, .inr x => B.label x
  | .neg A, x => A.label x

def subst (σ : P → Formula Q) : Formula P → Formula Q
  | .var p => σ p
  | .top => .top
  | .bot => .bot
  | .conj A B => .conj (A.subst σ) (B.subst σ)
  | .disj A B => .disj (A.subst σ) (B.subst σ)
  | .neg A => .neg (A.subst σ)

/-- An old position together with a position in its own substituted copy. -/
def Block (σ : P → Formula Q) (A : Formula P) :=
  (x : A.Occ) × (σ (A.label x)).Occ

def expand (σ : P → Formula Q) : (A : Formula P) → (A.subst σ).Occ → A.Block σ
  | .var _, x => ⟨(), x⟩
  | .top, x => nomatch x
  | .bot, x => nomatch x
  | .conj A _, .inl x => ⟨.inl (expand σ A x).1, (expand σ A x).2⟩
  | .conj _ B, .inr x => ⟨.inr (expand σ B x).1, (expand σ B x).2⟩
  | .disj A _, .inl x => ⟨.inl (expand σ A x).1, (expand σ A x).2⟩
  | .disj _ B, .inr x => ⟨.inr (expand σ B x).1, (expand σ B x).2⟩
  | .neg A, x => expand σ A x

def contract (σ : P → Formula Q) : (A : Formula P) → A.Block σ → (A.subst σ).Occ
  | .var _, ⟨_,t⟩ => t
  | .top, ⟨x,_⟩ => nomatch x
  | .bot, ⟨x,_⟩ => nomatch x
  | .conj A _, ⟨.inl r,t⟩ => .inl (contract σ A ⟨r,t⟩)
  | .conj _ B, ⟨.inr r,t⟩ => .inr (contract σ B ⟨r,t⟩)
  | .disj A _, ⟨.inl r,t⟩ => .inl (contract σ A ⟨r,t⟩)
  | .disj _ B, ⟨.inr r,t⟩ => .inr (contract σ B ⟨r,t⟩)
  | .neg A, x => contract σ A x

theorem contract_expand (σ : P → Formula Q) (A : Formula P) (x : (A.subst σ).Occ) :
    A.contract σ (A.expand σ x) = x := by
  induction A with
  | var p => rfl
  | top => exact Empty.elim x
  | bot => exact Empty.elim x
  | conj A B ihA ihB =>
    cases x with
    | inl x =>
      change Sum.inl (A.contract σ (A.expand σ x)) = Sum.inl x
      exact congrArg Sum.inl (ihA x)
    | inr x =>
      change Sum.inr (B.contract σ (B.expand σ x)) = Sum.inr x
      exact congrArg Sum.inr (ihB x)
  | disj A B ihA ihB =>
    cases x with
    | inl x =>
      change Sum.inl (A.contract σ (A.expand σ x)) = Sum.inl x
      exact congrArg Sum.inl (ihA x)
    | inr x =>
      change Sum.inr (B.contract σ (B.expand σ x)) = Sum.inr x
      exact congrArg Sum.inr (ihB x)
  | neg A ih => exact ih x

theorem expand_contract (σ : P → Formula Q) (A : Formula P) (x : A.Block σ) :
    A.expand σ (A.contract σ x) = x := by
  induction A with
  | var p => cases x with | mk r t => cases r; rfl
  | top => exact Empty.elim x.1
  | bot => exact Empty.elim x.1
  | conj A B ihA ihB =>
    cases x with
    | mk r t =>
      cases r with
      | inl r =>
        exact congrArg (fun z : A.Block σ => (⟨Sum.inl z.1, z.2⟩ : (conj A B).Block σ))
          (ihA ⟨r,t⟩)
      | inr r =>
        exact congrArg (fun z : B.Block σ => (⟨Sum.inr z.1, z.2⟩ : (conj A B).Block σ))
          (ihB ⟨r,t⟩)
  | disj A B ihA ihB =>
    cases x with
    | mk r t =>
      cases r with
      | inl r =>
        exact congrArg (fun z : A.Block σ => (⟨Sum.inl z.1, z.2⟩ : (disj A B).Block σ))
          (ihA ⟨r,t⟩)
      | inr r =>
        exact congrArg (fun z : B.Block σ => (⟨Sum.inr z.1, z.2⟩ : (disj A B).Block σ))
          (ihB ⟨r,t⟩)
  | neg A ih => exact ih x

theorem repeated_positions_distinct (p : P) :
    (Sum.inl () : (conj (var p) (var p)).Occ) ≠ Sum.inr () := by
  intro h
  cases h

end Formula

end DosenPetric
