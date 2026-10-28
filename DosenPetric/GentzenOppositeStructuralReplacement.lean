module

public import DosenPetric.GentzenSelectedOppositeStructural
public import DosenPetric.GentzenSameSideLogicalDescent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace CutCommutation

/-- Reconstruct the opposite antecedent program after eliminating its actual child cut. -/
theorem selected_opposite_left_eliminated {F U Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (f : G P U Δ) (x : At Δ C)
    (g : G P Θ Λ) (y : At Θ C) (hs : PositionalCut.Eliminated f x g y) :
    PositionalCut.Eliminated (p.left f) x g y := by
  obtain ⟨a,ha,_,ea⟩ := hs
  let q := p.prefixFixed y.erase
  let b := q.left a
  have hb : b.CutFree := by
    change b.cutCount = 0
    rw [StructuralProgram.left_count]
    exact ha
  refine ⟨G.atomize b,G.atomize_cutFree b hb,G.atomize_atomized b,?_⟩
  have eb : ofTerm b.denote = ofTerm (q.left (PositionalCut.cut f x g y)).denote := by
    simpa only [b,StructuralProgram.left_denote] using
      congrArg (fun k => comp (q.arrow .conj) k) ea
  exact (G.atomize_denote b).trans (eb.trans (selected_opposite_left p f x g y).symm)

/-- Reconstruct the independently typed opposite succedent program. -/
theorem selected_opposite_right_eliminated {Γ Δ Θ F U : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (f : G P Γ Δ) (x : At Δ C)
    (g : G P Θ U) (y : At Θ C) (hs : PositionalCut.Eliminated f x g y) :
    PositionalCut.Eliminated f x (p.right g) y := by
  obtain ⟨a,ha,_,ea⟩ := hs
  let q := p.suffixFixed x.erase
  let b := q.right a
  have hb : b.CutFree := by
    change b.cutCount = 0
    rw [StructuralProgram.right_count]
    exact ha
  refine ⟨G.atomize b,G.atomize_cutFree b hb,G.atomize_atomized b,?_⟩
  have eb : ofTerm b.denote = ofTerm (q.right (PositionalCut.cut f x g y)).denote := by
    simpa only [b,StructuralProgram.right_denote] using
      congrArg (fun k => comp k (q.arrow .disj)) ea
  exact (G.atomize_denote b).trans (eb.trans (selected_opposite_right p f x g y).symm)

theorem selected_opposite_left_rank_step {F U Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (hp : 0 < p.steps) (f : G P U Δ) (x : At Δ C)
    (g : G P Θ Λ) (y : At Θ C) (hc : PositionalCut.Clean (p.left f) x g y)
    (ih : ∀ {I J K L : List (NormalForm P)} (a : G P I J) (v : At J C)
      (b : G P K L) (w : At K C),
      PositionalCut.rank a v b w < PositionalCut.rank (p.left f) x g y →
      PositionalCut.Clean a v b w → PositionalCut.Eliminated a v b w) :
    PositionalCut.Eliminated (p.left f) x g y := by
  have hd := PositionalCut.selected_opposite_left_descent p hp f x g y hc
  exact selected_opposite_left_eliminated p f x g y (ih f x g y hd.2 hd.1)

theorem selected_opposite_right_rank_step {Γ Δ Θ F U : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (hp : 0 < p.steps) (f : G P Γ Δ) (x : At Δ C)
    (g : G P Θ U) (y : At Θ C) (hc : PositionalCut.Clean f x (p.right g) y)
    (ih : ∀ {I J K L : List (NormalForm P)} (a : G P I J) (v : At J C)
      (b : G P K L) (w : At K C),
      PositionalCut.rank a v b w < PositionalCut.rank f x (p.right g) y →
      PositionalCut.Clean a v b w → PositionalCut.Eliminated a v b w) :
    PositionalCut.Eliminated f x (p.right g) y := by
  have hd := PositionalCut.selected_opposite_right_descent p hp f x g y hc
  exact selected_opposite_right_eliminated p f x g y (ih f x g y hd.2 hd.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
