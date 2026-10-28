module

public import DosenPetric.GentzenSuffixedLogicalRules

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace CutCommutation

/-- Commute disjunction-right in the opposite cut premise at arbitrary selected gaps. -/
theorem opposite_disjR {Γ Δ Θ F U : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ (F ++ A :: B :: U)) (y : At Θ C) :
    ofTerm (PositionalCut.cut f x (G.disjR Θ F U A B g) y).denote =
      ofTerm (SuffixedLogical.disjR (y.erase ++ Γ) F U x.erase A B
        (PositionalCut.cut f x g y)).denote := by
  rw [PositionalCut.splice_denote,G.denote_disjR,disjRight_compare,
    SuffixedLogical.disjR_denote,PositionalCut.splice_denote]
  change comp _ (comp (splice _ (comp (y.toHead.arrow .conj)
    (comp (ofTerm g.denote) (logicalSide .disj F U A B)))) _) = _
  rw [← Laws.assoc (y.toHead.arrow .conj),Splice.output]
  have he : comp (ofTerm (append .disj (F ++ A :: B :: U) x.erase).toTerm)
      (suffixLogicalSide .disj F U x.erase A B) =
      comp (tensor .disj (logicalSide .disj F U A B) (id (succ x.erase)))
        (ofTerm (append .disj (F ++ .disj A B :: U) x.erase).toTerm) :=
    suffixLogicalSide_split .disj F U x.erase A B
  simp only [Laws.assoc]
  rw [he]

theorem opposite_disjR_eliminated {Γ Δ Θ F U : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ (F ++ A :: B :: U)) (y : At Θ C)
    (hs : PositionalCut.Eliminated f x g y) :
    PositionalCut.Eliminated f x (G.disjR Θ F U A B g) y := by
  obtain ⟨a,ha,aa,ea⟩ := hs
  refine ⟨SuffixedLogical.disjR (y.erase ++ Γ) F U x.erase A B a,?_,?_,?_⟩
  · change (SuffixedLogical.disjR (y.erase ++ Γ) F U x.erase A B a).cutCount = 0
    rw [SuffixedLogical.disjR_count]
    exact ha
  · exact (SuffixedLogical.disjR_atomized ..).mpr aa
  · have he := congrArg (fun k => comp k (suffixLogicalSide .disj F U x.erase A B)) ea
    have hh : ofTerm (SuffixedLogical.disjR (y.erase ++ Γ) F U x.erase A B a).denote =
        ofTerm (SuffixedLogical.disjR (y.erase ++ Γ) F U x.erase A B (PositionalCut.cut f x g y)).denote := by
      simpa only [SuffixedLogical.disjR_denote] using he
    exact hh.trans (opposite_disjR f x g y).symm

end CutCommutation
end DosenPetric.Reduced.Gentzen
