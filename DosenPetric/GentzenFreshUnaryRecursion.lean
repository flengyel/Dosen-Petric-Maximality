module

public import DosenPetric.GentzenBlockedRightGammaConjRank
public import DosenPetric.GentzenFreshPrincipals

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.PositionalCut
universe u
variable {P : Type u}

theorem rank_fresh_conjL {Γ Δ F U V : List (NormalForm P)} {A B : NormalForm P}
    (h : G P Γ Δ) (z : At Δ (.conj A B)) (g : G P (F++A::B::U) V) :
    rank h z (G.conjL F U V A B g) (At.shift F (.here (.conj A B) U)) = h.rho .right z+1 := by
  unfold rank
  rw [G.rho_conjL_principal]

theorem clean_fresh_conjL {Γ Δ F U V : List (NormalForm P)} {A B : NormalForm P}
    (h : G P Γ Δ) (z : At Δ (.conj A B)) (g : G P (F++A::B::U) V)
    (hh : h.CutFree) (ah : h.Atomized) (bh : AllBlockedAt h .right z)
    (hg : g.CutFree) (ag : g.Atomized) :
    Clean h z (G.conjL F U V A B g) (At.shift F (.here (.conj A B) U)) :=
  ⟨hh,hg,ah,ag,bh,G.conjL_principal_blocked F U V A B g⟩

theorem rank_fresh_conjL_lt {Γ Δ Θ Λ F U V : List (NormalForm P)} {A B : NormalForm P}
    (h : G P Γ Δ) (z : At Δ (.conj A B)) (old : G P Θ Λ) (y : At Θ (.conj A B))
    (hold : 1 < old.rho .left y) (g : G P (F++A::B::U) V) :
    rank h z (G.conjL F U V A B g) (At.shift F (.here (.conj A B) U)) < rank h z old y := by
  rw [rank_fresh_conjL]
  unfold rank
  omega

end DosenPetric.Reduced.Gentzen.PositionalCut
