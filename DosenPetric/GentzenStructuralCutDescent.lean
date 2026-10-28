module

public import DosenPetric.GentzenStructuralAddresses

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PositionalCut

/-- Cleanliness is inherited at the original upper position through the actual structural address. -/
theorem clean_same_right {F U Γ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (x : At F C) (y : At U C) (hy : p.get y = x)
    (f : G P Γ U) (g : G P Θ Λ) (z : At Θ C)
    (hc : Clean (p.right f) x g z) : Clean f y g z := by
  rcases hc with ⟨hf,hg,af,ag,bf,bg⟩
  refine ⟨(p.rightAddress f).cutFree hf,hg,(p.rightAddress f).atomized af,ag,?_,bg⟩
  apply bf.inherit (p.rightAddress f) y
  rw [StructuralProgram.rightAddress_ascend,hy]

theorem clean_same_left {F U Γ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (x : At F C) (y : At U C) (hy : p.get y = x)
    (f : G P Γ Δ) (z : At Δ C) (g : G P U Λ)
    (hc : Clean f z (p.left g) x) : Clean f z g y := by
  rcases hc with ⟨hf,hg,af,ag,bf,bg⟩
  refine ⟨hf,(p.leftAddress g).cutFree hg,af,(p.leftAddress g).atomized ag,bf,?_⟩
  apply bg.inherit (p.leftAddress g) y
  rw [StructuralProgram.leftAddress_ascend,hy]

/-- Structural steps lower the original selected rank; no head-routing rank is substituted. -/
theorem rank_same_right {F U Γ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (hp : 0 < p.steps) (x : At F C) (y : At U C)
    (hy : p.get y = x) (f : G P Γ U) (g : G P Θ Λ) (z : At Θ C) :
    rank f y g z < rank (p.right f) x g z := by
  have hn : (p.rightAddress f).path ≠ [] := by
    intro he
    have hl := p.rightAddress_length f
    rw [he] at hl
    simp only [List.length_nil] at hl
    omega
  have ha : (p.rightAddress f).ascend .right y = some x := by
    rw [StructuralProgram.rightAddress_ascend,hy]
  have hr := (p.rightAddress f).ascend_rank_lt .right x y ha hn
  unfold rank
  omega

theorem rank_same_left {F U Γ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (hp : 0 < p.steps) (x : At F C) (y : At U C)
    (hy : p.get y = x) (f : G P Γ Δ) (z : At Δ C) (g : G P U Λ) :
    rank f z g y < rank f z (p.left g) x := by
  have hn : (p.leftAddress g).path ≠ [] := by
    intro he
    have hl := p.leftAddress_length g
    rw [he] at hl
    simp only [List.length_nil] at hl
    omega
  have ha : (p.leftAddress g).ascend .left y = some x := by
    rw [StructuralProgram.leftAddress_ascend,hy]
  have hr := (p.leftAddress g).ascend_rank_lt .left x y ha hn
  unfold rank
  omega

end PositionalCut
namespace CutCommutation

/-- The same-side right structural branch of the clean selected-rank induction. -/
theorem same_right_rank_step {F U Γ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (hp : 0 < p.steps) (x : At F C) (y : At U C)
    (h : p.route.SingleFiber x y) (f : G P Γ U) (g : G P Θ Λ) (z : At Θ C)
    (hc : PositionalCut.Clean (p.right f) x g z)
    (ih : ∀ {I J K L : List (NormalForm P)} (a : G P I J) (v : At J C)
      (b : G P K L) (w : At K C),
      PositionalCut.rank a v b w < PositionalCut.rank (p.right f) x g z →
      PositionalCut.Clean a v b w → PositionalCut.Eliminated a v b w) :
    PositionalCut.Eliminated (p.right f) x g z := by
  have hy : p.get y = x := by simpa only [StructuralProgram.route_get] using h.1
  apply same_right_eliminated p x y h f g z
  exact ih f y g z (PositionalCut.rank_same_right p hp x y hy f g z)
    (PositionalCut.clean_same_right p x y hy f g z hc)

/-- The same-side left structural branch with the separately typed original-rank bound. -/
theorem same_left_rank_step {F U Γ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (hp : 0 < p.steps) (x : At F C) (y : At U C)
    (h : p.route.SingleFiber x y) (f : G P Γ Δ) (z : At Δ C) (g : G P U Λ)
    (hc : PositionalCut.Clean f z (p.left g) x)
    (ih : ∀ {I J K L : List (NormalForm P)} (a : G P I J) (v : At J C)
      (b : G P K L) (w : At K C),
      PositionalCut.rank a v b w < PositionalCut.rank f z (p.left g) x →
      PositionalCut.Clean a v b w → PositionalCut.Eliminated a v b w) :
    PositionalCut.Eliminated f z (p.left g) x := by
  have hy : p.get y = x := by simpa only [StructuralProgram.route_get] using h.1
  apply same_left_eliminated p x y h f z g
  exact ih f z g y (PositionalCut.rank_same_left p hp x y hy f z g)
    (PositionalCut.clean_same_left p x y hy f z g hc)

end CutCommutation
end DosenPetric.Reduced.Gentzen
