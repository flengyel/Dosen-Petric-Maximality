module

public import DosenPetric.GentzenPrefixedLogicalRules

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace CutCommutation

/-- Commute conjunction-left in the opposite cut premise at arbitrary selected gaps. -/
theorem opposite_conjL {F U Δ Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (F ++ A :: B :: U) Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C) :
    ofTerm (PositionalCut.cut (G.conjL F U Δ A B f) x g y).denote =
      ofTerm (PrefixedLogical.conjL y.erase F U (Λ ++ x.erase) A B
        (PositionalCut.cut f x g y)).denote := by
  rw [PositionalCut.splice_denote,G.denote_conjL,conjLeft_compare,
    PrefixedLogical.conjL_denote,PositionalCut.splice_denote]
  change comp _ (comp (splice (comp (comp (logicalSide .conj F U A B) (ofTerm f.denote)) _)
    (comp _ (ofTerm g.denote))) _) = _
  rw [Laws.assoc (logicalSide .conj F U A B),Splice.input]
  have he : comp (prefixSide .conj y.erase (logicalSide .conj F U A B))
      (ofTerm (append .conj y.erase (F ++ A :: B :: U)).invTerm) =
      comp (ofTerm (append .conj y.erase (F ++ .conj A B :: U)).invTerm)
        (tensor .conj (id (ante y.erase)) (logicalSide .conj F U A B)) :=
    prefixSide_split .conj y.erase _
  simp only [Laws.assoc]
  rw [← Laws.assoc (prefixSide .conj y.erase (logicalSide .conj F U A B)),he,Laws.assoc]

/-- Rebuild the same cut-free atomized representative below the opposite conjunction rule. -/
theorem opposite_conjL_eliminated {F U Δ Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (F ++ A :: B :: U) Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hs : PositionalCut.Eliminated f x g y) :
    PositionalCut.Eliminated (G.conjL F U Δ A B f) x g y := by
  obtain ⟨a,ha,aa,ea⟩ := hs
  refine ⟨PrefixedLogical.conjL y.erase F U (Λ ++ x.erase) A B a,?_,?_,?_⟩
  · change (PrefixedLogical.conjL y.erase F U (Λ ++ x.erase) A B a).cutCount = 0
    rw [PrefixedLogical.conjL_count]
    exact ha
  · exact (PrefixedLogical.conjL_atomized ..).mpr aa
  · have he := congrArg (fun k => comp (prefixSide .conj y.erase (logicalSide .conj F U A B)) k) ea
    have hh : ofTerm (PrefixedLogical.conjL y.erase F U (Λ ++ x.erase) A B a).denote =
        ofTerm (PrefixedLogical.conjL y.erase F U (Λ ++ x.erase) A B (PositionalCut.cut f x g y)).denote := by
      simpa only [PrefixedLogical.conjL_denote] using he
    exact hh.trans (opposite_conjL f x g y).symm

end CutCommutation
end DosenPetric.Reduced.Gentzen
