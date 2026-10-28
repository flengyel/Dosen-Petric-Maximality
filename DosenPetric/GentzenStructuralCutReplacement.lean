module

public import DosenPetric.GentzenStructuralSingleFibers

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace CutCommutation

/-- Rebuild a same-side structural cut after its smaller selected subcut is eliminated. -/
theorem same_right_eliminated {F U Γ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (x : At F C) (y : At U C)
    (h : p.route.SingleFiber x y) (f : G P Γ U) (g : G P Θ Λ) (z : At Θ C)
    (hs : PositionalCut.Eliminated f y g z) : PositionalCut.Eliminated (p.right f) x g z := by
  obtain ⟨a,ha,_,ea⟩ := hs
  let q := (p.residual x y h).prefixFixed Λ
  let b := q.right a
  have hb : b.CutFree := by
    change b.cutCount = 0
    rw [StructuralProgram.right_count]
    exact ha
  refine ⟨G.atomize b, G.atomize_cutFree b hb, G.atomize_atomized b, ?_⟩
  have eb : ofTerm b.denote = ofTerm (q.right (PositionalCut.cut f y g z)).denote := by
    simpa only [StructuralProgram.right_denote, b] using
      congrArg (fun k => comp k (q.arrow .disj)) ea
  exact (G.atomize_denote b).trans (eb.trans (same_right p x y h f g z).symm)

/-- Rebuild the independently typed left-side structural case at the same original sequent. -/
theorem same_left_eliminated {F U Γ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (x : At F C) (y : At U C)
    (h : p.route.SingleFiber x y) (f : G P Γ Δ) (z : At Δ C) (g : G P U Λ)
    (hs : PositionalCut.Eliminated f z g y) : PositionalCut.Eliminated f z (p.left g) x := by
  obtain ⟨a,ha,_,ea⟩ := hs
  let q := (p.residual x y h).suffixFixed Γ
  let b := q.left a
  have hb : b.CutFree := by
    change b.cutCount = 0
    rw [StructuralProgram.left_count]
    exact ha
  refine ⟨G.atomize b, G.atomize_cutFree b hb, G.atomize_atomized b, ?_⟩
  have eb : ofTerm b.denote = ofTerm (q.left (PositionalCut.cut f z g y)).denote := by
    simpa only [StructuralProgram.left_denote, b] using
      congrArg (fun k => comp (q.arrow .conj) k) ea
  exact (G.atomize_denote b).trans (eb.trans (same_left p x y h f z g).symm)

end CutCommutation
end DosenPetric.Reduced.Gentzen
