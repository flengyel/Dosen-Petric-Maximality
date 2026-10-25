module

public import DosenPetric.GentzenEntryFrames

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.Premise
universe u
variable {P : Type u}

theorem mix_left_index {Γ Θ Δ Λ : List (NormalForm P)}
    (f : G P Γ Δ) (g : G P Θ Λ) {C : NormalForm P}
    (y : At Γ C) (x : At (Θ++Γ) C)
    (hy : (Premise.mix_left f g).parent .left y = some x) :
    Θ.length+y.index = x.index := by
  have hi := congrArg At.index (Option.some.inj hy)
  rw [At.index_shift] at hi
  exact hi

end DosenPetric.Reduced.Gentzen.Premise

namespace DosenPetric.Reduced.Gentzen.G
universe u
variable {P : Type u}

theorem lowerContraction_index_unique {Γ Δ : List (NormalForm P)} (g : G P Γ Δ)
    (s : SequentSide) {A B : NormalForm P} (x : Place s Γ Δ A) (y : Place s Γ Δ B)
    (hx : g.LowerContraction s x) (hy : g.LowerContraction s y) : x.index = y.index := by
  have h₀ := (g.lowerContraction_iff_arity s x).mp hx
  have h₁ := (g.lowerContraction_iff_arity s y).mp hy
  cases g <;> cases s <;> simp only [sourceArity] at h₀ h₁
  all_goals first | omega | (split at h₀ <;> split at h₁ <;> omega)

end DosenPetric.Reduced.Gentzen.G
