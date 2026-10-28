module

public import DosenPetric.GentzenSelectedCleanCuts

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PositionalCut

/-- Native rank after routing includes precisely the actual exchanges that were added. -/
theorem routed_rank {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C) :
    G.cutRank (x.toHead.right f) (y.toHead.left g) =
      rank f x g y + x.toHead.steps + y.toHead.steps := by
  unfold G.cutRank G.leftCutRank G.rightCutRank rank
  rw [← x.toHead_get, ← y.toHead_get, ExchangeScript.rho_right, ExchangeScript.rho_left]
  omega

theorem routed_rank_eq {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C) :
    G.cutRank (x.toHead.right f) (y.toHead.left g) =
      rank f x g y + (if x.index = 0 then 0 else 1) + (if y.index = 0 then 0 else 1) := by
  rw [routed_rank, At.toHead_steps, At.toHead_steps]

end PositionalCut
end DosenPetric.Reduced.Gentzen
