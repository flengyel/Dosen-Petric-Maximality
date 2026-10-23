module

public import DosenPetric.PositiveThinningAtomization

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- The side of a whole-formula position in a sequent. -/
inductive SequentSide where
  | left | right
  deriving DecidableEq

def SequentSide.context (s : SequentSide) (Γ Δ : List (NormalForm P)) : List (NormalForm P) :=
  match s with
  | .left => Γ
  | .right => Δ

abbrev Place (s : SequentSide) (Γ Δ : List (NormalForm P)) (C : NormalForm P) :=
  At (s.context Γ Δ) C

abbrev SidePos (Γ Δ : List (NormalForm P)) (C : NormalForm P) := At Γ C ⊕ At Δ C

namespace At

/-- Keep only the fixed prefix and tail, replacing the distinguished block.
    Positions inside that block have no image. -/
def fixed (Γ X Y Θ : List (NormalForm P)) {C : NormalForm P} :
    At (Γ ++ (X ++ Θ)) C → Option (At (Γ ++ (Y ++ Θ)) C) :=
  match Γ with
  | [] => fun a => match splitAppend X Θ a with
    | .inl _ => none
    | .inr b => some (shift Y b)
  | A :: Γ => fun a => match a with
    | .here _ _ => some (.here A _)
    | .there b => (fixed Γ X Y Θ b).map At.there

theorem fixed_before (Γ X Y Θ : List (NormalForm P)) {C : NormalForm P} (a : At Γ C) :
    fixed Γ X Y Θ (a.before (X ++ Θ)) = some (a.before (Y ++ Θ)) := by
  induction a with
  | here => rfl
  | there a ih => exact congrArg (Option.map At.there) ih

theorem fixed_middle (Γ X Y Θ : List (NormalForm P)) {C : NormalForm P} (a : At X C) :
    fixed Γ X Y Θ (shift Γ (a.before Θ)) = none := by
  induction Γ with
  | nil => simp only [fixed, shift, splitAppend_before]
  | cons A Γ ih => simp only [fixed, shift, ih, Option.map_none]

theorem fixed_tail (Γ X Y Θ : List (NormalForm P)) {C : NormalForm P} (a : At Θ C) :
    fixed Γ X Y Θ (shift Γ (shift X a)) = some (shift Γ (shift Y a)) := by
  induction Γ with
  | nil => simp only [fixed, shift, splitAppend_shift]
  | cons A Γ ih => simp only [fixed, shift, ih, Option.map_some]

/-- The two fixed-block maps are partial inverses on their fixed positions. -/
theorem fixed_reverse (Γ X Y Θ : List (NormalForm P)) {C : NormalForm P}
    (a : At (Γ ++ (X ++ Θ)) C) (b : At (Γ ++ (Y ++ Θ)) C) :
    fixed Γ X Y Θ a = some b ↔ fixed Γ Y X Θ b = some a := by
  cases cases_append Γ (X ++ Θ) a with
  | inl h =>
    obtain ⟨a, rfl⟩ := h
    rw [fixed_before]
    constructor
    · intro h; cases Option.some.inj h; exact fixed_before ..
    · intro h
      cases cases_append Γ (Y ++ Θ) b with
      | inl hb =>
        obtain ⟨b, rfl⟩ := hb
        rw [fixed_before] at h
        have hi := congrArg At.index (Option.some.inj h)
        simp only [index_before] at hi
        cases At.index_injective b a hi
        rfl
      | inr hb =>
        obtain ⟨b, rfl⟩ := hb
        cases cases_append Y Θ b with
        | inl hb => obtain ⟨b, rfl⟩ := hb; simp only [fixed_middle] at h; cases h
        | inr hb =>
          obtain ⟨b, rfl⟩ := hb
          rw [fixed_tail] at h
          have hi := congrArg At.index (Option.some.inj h)
          have hl := a.index_lt
          simp only [index_shift, index_before] at hi
          omega
  | inr h =>
    obtain ⟨a, rfl⟩ := h
    cases cases_append X Θ a with
    | inl ha =>
      obtain ⟨a, rfl⟩ := ha
      rw [fixed_middle]
      constructor
      · intro h; cases h
      · intro h
        exact False.elim (by
          cases cases_append Γ (Y ++ Θ) b with
          | inl hb =>
            obtain ⟨b, rfl⟩ := hb
            rw [fixed_before] at h
            have hi := congrArg At.index (Option.some.inj h)
            have hl := b.index_lt
            simp only [index_before, index_shift] at hi
            omega
          | inr hb =>
            obtain ⟨b, rfl⟩ := hb
            cases cases_append Y Θ b with
            | inl hb => obtain ⟨b, rfl⟩ := hb; rw [fixed_middle] at h; cases h
            | inr hb =>
              obtain ⟨b, rfl⟩ := hb
              rw [fixed_tail] at h
              have hi := congrArg At.index (Option.some.inj h)
              have hl := a.index_lt
              simp only [index_before, index_shift] at hi
              omega)
    | inr ha =>
      obtain ⟨a, rfl⟩ := ha
      rw [fixed_tail]
      constructor
      · intro h; cases Option.some.inj h; exact fixed_tail ..
      · intro h
        cases cases_append Γ (Y ++ Θ) b with
        | inl hb =>
          obtain ⟨b, rfl⟩ := hb
          rw [fixed_before] at h
          have hi := congrArg At.index (Option.some.inj h)
          have hl := b.index_lt
          simp only [index_before, index_shift] at hi
          omega
        | inr hb =>
          obtain ⟨b, rfl⟩ := hb
          cases cases_append Y Θ b with
          | inl hb => obtain ⟨b, rfl⟩ := hb; rw [fixed_middle] at h; cases h
          | inr hb =>
            obtain ⟨b, rfl⟩ := hb
            rw [fixed_tail] at h
            have hi := congrArg At.index (Option.some.inj h)
            simp only [index_shift] at hi
            have hab : b = a := At.index_injective b a (by omega)
            cases hab
            rfl

end At
end DosenPetric.Reduced.Gentzen
