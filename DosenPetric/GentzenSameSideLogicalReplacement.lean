module

public import DosenPetric.GentzenSameSideLogicalTail

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace CutCommutation

/-- Rebuild the eliminated actual child below the native conjunction-left prefix rule. -/
theorem same_conjL_before_eliminated {Γ Δ F U Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P (F ++ A :: B :: U) Λ) (a : At F C)
    (hs : PositionalCut.Eliminated f x g (a.before (A :: B :: U))) :
    PositionalCut.Eliminated f x (G.conjL F U Λ A B g) (a.before (.conj A B :: U)) := by
  obtain ⟨b,hb,ab,ea⟩ := hs
  refine ⟨SameSideLogical.conjBefore a b,?_,?_,?_⟩
  · change (SameSideLogical.conjBefore a b).cutCount = 0
    simpa only [SameSideLogical.conjBefore,G.count_reindex,SuffixedLogical.conjL_count,G.CutFree] using hb
  · simpa only [SameSideLogical.conjBefore,G.atomized_reindex,SuffixedLogical.conjL_atomized] using ab
  · have he : ofTerm (SameSideLogical.conjBefore a b).denote =
        ofTerm (SameSideLogical.conjBefore a (PositionalCut.cut f x g (a.before (A :: B :: U)))).denote := by
      unfold SameSideLogical.conjBefore
      apply G.reindex_congr
      rw [SuffixedLogical.conjL_denote,SuffixedLogical.conjL_denote]
      exact congrArg (fun k => comp (suffixLogicalSide .conj a.erase U Γ A B) k) (G.reindex_congr (congrArg (fun xs => xs ++ Γ) (a.erase_before (A :: B :: U))) rfl ea)
    exact he.trans (same_conjL_before f x g a).symm

/-- Rebuild the eliminated actual child below the native conjunction-left suffix rule. -/
theorem same_conjL_tail_eliminated {Γ Δ F U Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P (F ++ A :: B :: U) Λ) (a : At U C)
    (hs : PositionalCut.Eliminated f x g (At.shift F (At.shift [A,B] a))) :
    PositionalCut.Eliminated f x (G.conjL F U Λ A B g) (At.shift F (At.shift [.conj A B] a)) := by
  obtain ⟨b,hb,ab,ea⟩ := hs
  refine ⟨SameSideLogical.conjTail a b,?_,?_,?_⟩
  · change (SameSideLogical.conjTail a b).cutCount = 0
    simpa only [SameSideLogical.conjTail,G.count_reindex,SuffixedLogical.conjL_count,G.CutFree] using hb
  · simpa only [SameSideLogical.conjTail,G.atomized_reindex,SuffixedLogical.conjL_atomized] using ab
  · have he : ofTerm (SameSideLogical.conjTail a b).denote =
        ofTerm (SameSideLogical.conjTail a (PositionalCut.cut f x g (At.shift F (At.shift [A,B] a)))).denote := by
      unfold SameSideLogical.conjTail
      apply G.reindex_congr
      rw [SuffixedLogical.conjL_denote,SuffixedLogical.conjL_denote]
      exact congrArg (fun k => comp (suffixLogicalSide .conj F a.erase Γ A B) k) (G.reindex_congr (congrArg (fun xs => xs ++ Γ) (At.erase_shift_twice F [A,B] a)) rfl ea)
    exact he.trans (same_conjL_tail f x g a).symm

/-- Rebuild the eliminated actual child below the native disjunction-right prefix rule. -/
theorem same_disjR_before_eliminated {Γ F U Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (F ++ A :: B :: U)) (a : At F C) (g : G P Θ Λ) (y : At Θ C)
    (hs : PositionalCut.Eliminated f (a.before (A :: B :: U)) g y) :
    PositionalCut.Eliminated (G.disjR Γ F U A B f) (a.before (.disj A B :: U)) g y := by
  obtain ⟨b,hb,ab,ea⟩ := hs
  refine ⟨SameSideLogical.disjBefore a b,?_,?_,?_⟩
  · change (SameSideLogical.disjBefore a b).cutCount = 0
    simpa only [SameSideLogical.disjBefore,G.count_reindex,PrefixedLogical.disjR_count,G.CutFree] using hb
  · simpa only [SameSideLogical.disjBefore,G.atomized_reindex,PrefixedLogical.disjR_atomized] using ab
  · have he : ofTerm (SameSideLogical.disjBefore a b).denote =
        ofTerm (SameSideLogical.disjBefore a (PositionalCut.cut f (a.before (A :: B :: U)) g y)).denote := by
      unfold SameSideLogical.disjBefore
      apply G.reindex_congr
      rw [PrefixedLogical.disjR_denote,PrefixedLogical.disjR_denote]
      exact congrArg (fun k => comp k (prefixSide .disj Λ (logicalSide .disj a.erase U A B))) (G.reindex_congr rfl (congrArg (fun xs => Λ ++ xs) (a.erase_before (A :: B :: U))) ea)
    exact he.trans (same_disjR_before f a g y).symm

/-- Rebuild the eliminated actual child below the native disjunction-right suffix rule. -/
theorem same_disjR_tail_eliminated {Γ F U Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (F ++ A :: B :: U)) (a : At U C) (g : G P Θ Λ) (y : At Θ C)
    (hs : PositionalCut.Eliminated f (At.shift F (At.shift [A,B] a)) g y) :
    PositionalCut.Eliminated (G.disjR Γ F U A B f) (At.shift F (At.shift [.disj A B] a)) g y := by
  obtain ⟨b,hb,ab,ea⟩ := hs
  refine ⟨SameSideLogical.disjTail a b,?_,?_,?_⟩
  · change (SameSideLogical.disjTail a b).cutCount = 0
    simpa only [SameSideLogical.disjTail,G.count_reindex,PrefixedLogical.disjR_count,G.CutFree] using hb
  · simpa only [SameSideLogical.disjTail,G.atomized_reindex,PrefixedLogical.disjR_atomized] using ab
  · have he : ofTerm (SameSideLogical.disjTail a b).denote =
        ofTerm (SameSideLogical.disjTail a (PositionalCut.cut f (At.shift F (At.shift [A,B] a)) g y)).denote := by
      unfold SameSideLogical.disjTail
      apply G.reindex_congr
      rw [PrefixedLogical.disjR_denote,PrefixedLogical.disjR_denote]
      exact congrArg (fun k => comp k (prefixSide .disj Λ (logicalSide .disj F a.erase A B))) (G.reindex_congr rfl (congrArg (fun xs => Λ ++ xs) (At.erase_shift_twice F [A,B] a)) ea)
    exact he.trans (same_disjR_tail f a g y).symm

end CutCommutation
end DosenPetric.Reduced.Gentzen
