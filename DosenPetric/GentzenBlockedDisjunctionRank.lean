module

public import DosenPetric.GentzenBlockedDisjunctionDescent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SequentialDisjunction

theorem fresh_congr {F D J : List (NormalForm P)} {A B : NormalForm P}
    (k k' : G P F (J++A::B::D)) (he : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (fresh k).denote = ofTerm (fresh k').denote := by
  apply G.reindex_congr
  rw [G.denote_disjR,G.denote_disjR,ExchangeScript.right_denote,ExchangeScript.right_denote,he]

end SequentialDisjunction
namespace CutCommutation

theorem blockedR_disjunction_rank_step {A B : NormalForm P} {F X Y I J : List (NormalForm P)}
    (f : G P F (A::B::(X++.disj A B::Y))) (h : G P I J) (z : At I (.disj A B))
    (hc : PositionalCut.Clean (BlockedDisjunction.parent f) (BlockedDisjunction.block A B X Y).keep h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L (.disj A B))
      (d : G P M N) (w : At M (.disj A B)),
      PositionalCut.rank b v d w <
        PositionalCut.rank (BlockedDisjunction.parent f) (BlockedDisjunction.block A B X Y).keep h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (BlockedDisjunction.parent f) (BlockedDisjunction.block A B X Y).keep h z := by
  have hd := BlockedDisjunction.original_descent f h z hc
  have hs := ih f (.there (.there (BlockedDisjunction.parametric A B X Y))) h z hd.2 hd.1
  obtain ⟨k,hk,ak,ek⟩ := BlockedDisjunction.native_child_eliminated f h z hs
  have hf := SequentialDisjunction.fresh_clean k h z hk ak hc.2.1 hc.2.2.2.1 hc.2.2.2.2.2
  have hr := SequentialDisjunction.fresh_rank_lt k h z (BlockedDisjunction.parent f) _
    (BlockedDisjunction.contracted_rank_gt_one f h z hc)
  obtain ⟨l,hl,_,el⟩ := ih (SequentialDisjunction.fresh k) (.here (.disj A B) _) h z hr hf
  let t := SequentialRepair.prefixRouted (.disj A B) (BlockedDisjunction.residue A B X Y) l
  have ht : t.CutFree := by
    change t.cutCount = 0
    rw [SequentialRepair.prefixRouted_count]
    exact hl
  refine ⟨G.atomize t,G.atomize_cutFree t ht,G.atomize_atomized t,?_⟩
  apply (G.atomize_denote t).trans
  apply (SequentialRepair.prefixRouted_congr _ _ _ _ el).trans
  apply (SequentialRepair.prefixRouted_congr _ _ _ _ ?_).trans
  · exact (BlockedDisjunction.source_equation f h z).symm
  · exact Rules.cut_congr (SequentialDisjunction.fresh_congr _ _ ek) rfl

end CutCommutation
end DosenPetric.Reduced.Gentzen
