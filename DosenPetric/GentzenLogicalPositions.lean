module

public import DosenPetric.GentzenGapLogicalIndices

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace At

theorem option_index_injective {Γ : List (NormalForm P)} {E : NormalForm P}
    (a b : Option (At Γ E)) (h : a.map At.index = b.map At.index) : a = b := by
  cases a with
  | none => cases b with | none => rfl | some b => cases h
  | some a => cases b with
    | none => cases h
    | some b => exact congrArg some (index_injective a b (Option.some.inj h))

theorem fixed_index (Γ X Y Θ : List (NormalForm P)) {E : NormalForm P}
    (a : At (Γ ++ (X ++ Θ)) E) :
    (fixed Γ X Y Θ a).map At.index = GapLogical.parentIndex Γ.length X.length Y.length a.index := by
  cases cases_append Γ (X ++ Θ) a with
  | inl h =>
    obtain ⟨a,rfl⟩ := h
    rw [fixed_before,Option.map_some]
    simp only [index_before]
    exact (GapLogical.parent_before _ _ _ _ a.index_lt).symm
  | inr h =>
    obtain ⟨a,rfl⟩ := h
    cases cases_append X Θ a with
    | inl h =>
      obtain ⟨a,rfl⟩ := h
      rw [fixed_middle,Option.map_none,index_shift,index_before]
      have hl := a.index_lt
      unfold GapLogical.parentIndex
      repeat first | split | rfl | omega
    | inr h =>
      obtain ⟨a,rfl⟩ := h
      rw [fixed_tail,Option.map_some,index_shift,index_shift,index_shift,index_shift]
      unfold GapLogical.parentIndex
      repeat first | split | simp only [Option.some.injEq] | omega

theorem fixed_injective (Γ X Y Θ : List (NormalForm P)) {E : NormalForm P}
    (a b : At (Γ ++ (X ++ Θ)) E) (z : At (Γ ++ (Y ++ Θ)) E)
    (ha : fixed Γ X Y Θ a = some z) (hb : fixed Γ X Y Θ b = some z) : a = b := by
  have h0 := (fixed_reverse Γ X Y Θ a z).mp ha
  have h1 := (fixed_reverse Γ X Y Θ b z).mp hb
  exact Option.some.inj (h0.symm.trans h1)

theorem fixed_survives (Γ X Y Θ : List (NormalForm P)) {E : NormalForm P}
    (a : At (Γ ++ (X ++ Θ)) E) (h : a.index < Γ.length ∨ Γ.length+X.length ≤ a.index) :
    ∃ b, fixed Γ X Y Θ a = some b := by
  have hi := fixed_index Γ X Y Θ a
  unfold GapLogical.parentIndex at hi
  cases he : fixed Γ X Y Θ a with
  | none => rw [he] at hi; simp only [Option.map_none] at hi; split at hi <;> (try split at hi) <;> (try cases hi) <;> omega
  | some b => exact ⟨b,rfl⟩

/-- Strict order only on actual surviving positions of the partial fixed map. -/
theorem fixed_strict (Γ X Y Θ : List (NormalForm P)) {E : NormalForm P}
    (a b : At (Γ ++ (X ++ Θ)) E) (a' b' : At (Γ ++ (Y ++ Θ)) E)
    (ha : fixed Γ X Y Θ a = some a') (hb : fixed Γ X Y Θ b = some b')
    (hab : a.index < b.index) : a'.index < b'.index := by
  have h0 := fixed_index Γ X Y Θ a
  have h1 := fixed_index Γ X Y Θ b
  rw [ha,Option.map_some] at h0
  rw [hb,Option.map_some] at h1
  unfold GapLogical.parentIndex at h0 h1
  split at h0 <;> (try split at h0) <;> split at h1 <;> (try split at h1)
  all_goals simp_all only [Option.some.injEq,Option.some_ne_none]
  all_goals omega

def fixedImage (Γ X Y Θ : List (NormalForm P)) {E : NormalForm P}
    (a : At (Γ ++ (X ++ Θ)) E) (h : a.index < Γ.length ∨ Γ.length+X.length ≤ a.index) :
    At (Γ ++ (Y ++ Θ)) E := (fixed Γ X Y Θ a).get (by
      obtain ⟨b,hb⟩ := fixed_survives Γ X Y Θ a h
      rw [hb]
      rfl)

theorem fixedImage_spec (Γ X Y Θ : List (NormalForm P)) {E : NormalForm P}
    (a : At (Γ ++ (X ++ Θ)) E) (h : a.index < Γ.length ∨ Γ.length+X.length ≤ a.index) :
    fixed Γ X Y Θ a = some (fixedImage Γ X Y Θ a h) := (Option.some_get _).symm

end At
end DosenPetric.Reduced.Gentzen
