module

public import DosenPetric.GentzenCleanRankInduction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Unrestricted head-cut elimination for arbitrary cut-free premises, by degree. -/
theorem head_cut_elimination (C : NormalForm P)
    {Γ Δ Θ Λ : List (NormalForm P)} (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ)
    (hf : f.CutFree) (hg : g.CutFree) :
    ∃ h : G P (Θ ++ Γ) (Λ ++ Δ),
      h.CutFree ∧ h.Atomized ∧ ofTerm h.denote = ofTerm (G.cut f g).denote := by
  have hall : ∀ n : Nat, ∀ (D : NormalForm P), cutDegree D = n →
      ∀ {K L M N : List (NormalForm P)} (a : G P K (D :: L)) (b : G P (D :: M) N),
      a.CutFree → b.CutFree →
      ∃ h : G P (M ++ K) (N ++ L),
        h.CutFree ∧ h.Atomized ∧ ofTerm h.denote = ofTerm (G.cut a b).denote := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro D he K L M N a b ha hb
      have hd : DegreeBelow P (cutDegree D) := by
        intro E hE I J U V c d hc hd
        exact ih (cutDegree E) (by rw [← he]; exact hE) E rfl c d hc hd
      exact PositionalCut.cutFree_degree_step hd a (.here D L) b (.here D M) ha hb
  exact hall (cutDegree C) C rfl f g hf hg

namespace PositionalCut

/-- Every cut-free positional pair has an exact-output cut-free atomized representative. -/
theorem cutFree_elimination {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hf : f.CutFree) (hg : g.CutFree) : Eliminated f x g y := by
  have hxf : (x.toHead.right f).CutFree := by
    change (x.toHead.right f).cutCount = 0
    rw [ExchangeScript.right_count]
    exact hf
  have hyg : (y.toHead.left g).CutFree := by
    change (y.toHead.left g).cutCount = 0
    rw [ExchangeScript.left_count]
    exact hg
  exact head_cut_elimination C (x.toHead.right f) (y.toHead.left g) hxf hyg

end PositionalCut
end DosenPetric.Reduced.Gentzen
