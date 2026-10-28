module

public import DosenPetric.GentzenSelectedPositions
public import DosenPetric.GentzenCutThinning

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace PositionalCut
variable {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}

/-- A cut on exact tagged slots, using only the existing exchange and cut rules. -/
def cut (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C) :
    G P (y.erase ++ Γ) (Λ ++ x.erase) :=
  G.cut (x.toHead.right f) (y.toHead.left g)

theorem head (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) :
    cut f (.here C Δ) g (.here C Θ) = G.cut f g := rfl

theorem count (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C) :
    (cut f x g y).cutCount = f.cutCount + g.cutCount + 1 := by
  simp only [cut, G.cutCount, ExchangeScript.right_count, ExchangeScript.left_count]

theorem atomized (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C) :
    (cut f x g y).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [cut, G.Atomized, ExchangeScript.right_atomized, ExchangeScript.left_atomized]

theorem denote (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C) :
    (cut f x g y).denote = Rules.cut (x.toHead.right f).denote (y.toHead.left g).denote := rfl

theorem congr {f f' : G P Γ Δ} (x : At Δ C) {g g' : G P Θ Λ} (y : At Θ C)
    (hf : ofTerm f.denote = ofTerm f'.denote) (hg : ofTerm g.denote = ofTerm g'.denote) :
    ofTerm (cut f x g y).denote = ofTerm (cut f' x g' y).denote := by
  apply Rules.cut_congr
  · simpa only [ExchangeScript.right_denote] using
      congrArg (fun k => comp k (x.toHead.arrow .disj)) hf
  · simpa only [ExchangeScript.left_denote] using
      congrArg (fun k => comp (y.toHead.arrow .conj) k) hg

/-- Measured on the original premises, before the routing exchanges are added. -/
def rank (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C) : Nat :=
  f.rho .right x + g.rho .left y

theorem rank_head (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) :
    rank f (.here C Δ) g (.here C Θ) = G.cutRank f g := rfl

theorem rank_ge_two (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C) :
    2 ≤ rank f x g y := by
  have hf := f.rho_pos .right x
  have hg := g.rho_pos .left y
  unfold rank
  omega

theorem rank_two_iff_leaves (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C) :
    rank f x g y = 2 ↔ f.Leaf .right x ∧ g.Leaf .left y := by
  rw [← f.rho_one_iff_leaf .right x, ← g.rho_one_iff_leaf .left y]
  have hf := f.rho_pos .right x
  have hg := g.rho_pos .left y
  unfold rank
  omega

end PositionalCut
end DosenPetric.Reduced.Gentzen
