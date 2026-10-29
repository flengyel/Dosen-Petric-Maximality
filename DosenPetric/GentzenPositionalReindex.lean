module

public import DosenPetric.GentzenBlockedRankDispatch

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PositionalCut

theorem rank_reindex {Γ Δ Θ Λ Γ' Δ' Θ' Λ' : List (NormalForm P)} {C : NormalForm P}
    (hΓ : Γ=Γ') (hΔ : Δ=Δ') (hΘ : Θ=Θ') (hΛ : Λ=Λ')
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C) :
    rank (f.reindex hΓ hΔ) (x.cast hΔ) (g.reindex hΘ hΛ) (y.cast hΘ) = rank f x g y := by
  cases hΓ; cases hΔ; cases hΘ; cases hΛ; rfl

theorem clean_reindex {Γ Δ Θ Λ Γ' Δ' Θ' Λ' : List (NormalForm P)} {C : NormalForm P}
    (hΓ : Γ=Γ') (hΔ : Δ=Δ') (hΘ : Θ=Θ') (hΛ : Λ=Λ')
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C) :
    Clean (f.reindex hΓ hΔ) (x.cast hΔ) (g.reindex hΘ hΛ) (y.cast hΘ) ↔ Clean f x g y := by
  cases hΓ; cases hΔ; cases hΘ; cases hΛ; rfl

theorem eliminated_reindex {Γ Δ Θ Λ Γ' Δ' Θ' Λ' : List (NormalForm P)} {C : NormalForm P}
    (hΓ : Γ=Γ') (hΔ : Δ=Δ') (hΘ : Θ=Θ') (hΛ : Λ=Λ')
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C) :
    Eliminated (f.reindex hΓ hΔ) (x.cast hΔ) (g.reindex hΘ hΛ) (y.cast hΘ) ↔ Eliminated f x g y := by
  cases hΓ; cases hΔ; cases hΘ; cases hΛ; rfl

end PositionalCut
namespace G

theorem lower_reindex_left {Γ Δ Γ' Δ' : List (NormalForm P)} {C : NormalForm P}
    (hΓ : Γ=Γ') (hΔ : Δ=Δ') (f : G P Γ Δ) (x : At Γ C) :
    (f.reindex hΓ hΔ).LowerContraction .left (x.cast hΓ) ↔ f.LowerContraction .left x := by
  cases hΓ; cases hΔ; rfl

end G
end DosenPetric.Reduced.Gentzen
