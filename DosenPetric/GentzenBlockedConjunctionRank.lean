module

public import DosenPetric.GentzenBlockedConjunctionDescent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SequentialConjunction

theorem fresh_congr {F D I R : List (NormalForm P)} {A B : NormalForm P}
    (k k' : G P ((A::B::F)++I) (D++R)) (he : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (fresh k).denote = ofTerm (fresh k').denote := by
  rw [fresh,fresh,G.denote_conjL,G.denote_conjL,he]

end SequentialConjunction
namespace CutCommutation

theorem blockedL_conjunction_rank_step {A B : NormalForm P} {X Y D I J : List (NormalForm P)}
    (f : G P ((X++.conj A B::Y)++[A,B]) D) (h : G P I J) (z : At J (.conj A B))
    (hc : PositionalCut.Clean h z (BlockedConjunction.parent f) (BlockedConjunction.block A B X Y).keep)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L (.conj A B))
      (d : G P M N) (w : At M (.conj A B)),
      PositionalCut.rank b v d w <
        PositionalCut.rank h z (BlockedConjunction.parent f) (BlockedConjunction.block A B X Y).keep →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (BlockedConjunction.parent f) (BlockedConjunction.block A B X Y).keep := by
  have hd := BlockedConjunction.original_descent f h z hc
  have hs := ih h z f ((BlockedConjunction.parametric A B X Y).before [A,B]) hd.2 hd.1
  obtain ⟨k,hk,ak,ek⟩ := BlockedConjunction.native_child_eliminated f h z hs
  have hf := BlockedConjunction.fresh_clean_and_rank f h z hc k hk ak
  obtain ⟨l,hl,_,el⟩ := ih h z (SequentialConjunction.fresh k) (.here (.conj A B) _) hf.2 hf.1
  let t := SequentialRepair.routed (.conj A B) (BlockedConjunction.residue A B X Y) l
  have ht : t.CutFree := by
    change t.cutCount = 0
    rw [SequentialRepair.routed_count]
    exact hl
  refine ⟨G.atomize t,G.atomize_cutFree t ht,G.atomize_atomized t,?_⟩
  apply (G.atomize_denote t).trans
  apply (SequentialRepair.routed_congr _ _ _ _ el).trans
  apply (SequentialRepair.routed_congr _ _ _ _ ?_).trans
  · exact (BlockedConjunction.source_equation f h z).symm
  · exact Rules.cut_congr rfl (SequentialConjunction.fresh_congr _ _ ek)

end CutCommutation
end DosenPetric.Reduced.Gentzen
