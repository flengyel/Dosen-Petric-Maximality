module

public import DosenPetric.GentzenBlockedDisjBothDescent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SequentialDisjBoth

theorem fresh_cutFree_atomized {F H D E I R : List (NormalForm P)} {A B : NormalForm P}
    (k : G P ((F++[A])++I) (D++R)) (l : G P ((H++[B])++I) (E++R))
    (hk : k.CutFree) (ak : k.Atomized) (hl : l.CutFree) (al : l.Atomized) :
    (fresh k l).CutFree ∧ (fresh k l).Atomized := by
  constructor
  · change (fresh k l).cutCount = 0
    simp only [fresh,G.cutCount,childResult,BlockedSource.headL_script,ExchangeScript.left_count]
    change k.cutCount+l.cutCount = 0
    change k.cutCount = 0 at hk
    change l.cutCount = 0 at hl
    omega
  · simpa only [fresh,G.Atomized,childResult,BlockedSource.headL_script,ExchangeScript.left_atomized]
      using And.intro ak al

theorem fresh_congr {F H D E I R : List (NormalForm P)} {A B : NormalForm P}
    (k k' : G P ((F++[A])++I) (D++R)) (l l' : G P ((H++[B])++I) (E++R))
    (ek : ofTerm k.denote = ofTerm k'.denote) (el : ofTerm l.denote = ofTerm l'.denote) :
    ofTerm (fresh k l).denote = ofTerm (fresh k' l').denote := by
  apply Rules.disjLeft_congr
  · simp only [childResult,BlockedSource.headL_script,ExchangeScript.left_denote,ek]
  · simp only [childResult,BlockedSource.headL_script,ExchangeScript.left_denote,el]

end SequentialDisjBoth
namespace BlockedDisjBoth

theorem fresh_clean_and_rank {A B : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E)
    (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Y Z T).keep)
    (k : G P (((BlockedMix.firstTag (.disj A B) X Y).erase++[A])++I) (D++z.erase))
    (l : G P (((BlockedMix.firstTag (.disj A B) Z T).erase++[B])++I) (E++z.erase))
    (hk : k.CutFree) (ak : k.Atomized) (hl : l.CutFree) (al : l.Atomized) :
    PositionalCut.Clean h z (SequentialDisjBoth.fresh k l) (.here (.disj A B) _) ∧
      PositionalCut.rank h z (SequentialDisjBoth.fresh k l) (.here (.disj A B) _) <
        PositionalCut.rank h z (parent f g) (block A B X Y Z T).keep := by
  have hf := SequentialDisjBoth.fresh_cutFree_atomized k l hk ak hl al
  refine ⟨⟨hc.1,hf.1,hc.2.2.1,hf.2,hc.2.2.2.2.1,
    G.disjL_principal_blocked _ _⟩,?_⟩
  exact PositionalCut.rank_fresh_disjL_lt h z (parent f g) _ (contracted_rank_gt_one f g h z hc) _ _

end BlockedDisjBoth
namespace CutCommutation

theorem blockedL_disjunctionBoth_rank_step {A B : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E)
    (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (BlockedDisjBoth.parent f g) (BlockedDisjBoth.block A B X Y Z T).keep)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L (.disj A B))
      (d : G P M N) (w : At M (.disj A B)),
      PositionalCut.rank b v d w <
        PositionalCut.rank h z (BlockedDisjBoth.parent f g) (BlockedDisjBoth.block A B X Y Z T).keep →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (BlockedDisjBoth.parent f g) (BlockedDisjBoth.block A B X Y Z T).keep := by
  have hd := BlockedDisjBoth.first_descent f g h z hc
  have he := BlockedDisjBoth.second_descent f g h z hc
  have hs := ih h z f ((BlockedMix.firstTag (.disj A B) X Y).before [A]) hd.2 hd.1
  have ht := ih h z g ((BlockedMix.firstTag (.disj A B) Z T).before [B]) he.2 he.1
  obtain ⟨k,hk,ak,ek⟩ := BlockedDisjBoth.child_eliminated (BlockedMix.firstTag (.disj A B) X Y) f h z hs
  obtain ⟨l,hl,al,el⟩ := BlockedDisjBoth.child_eliminated (BlockedMix.firstTag (.disj A B) Z T) g h z ht
  have hf := BlockedDisjBoth.fresh_clean_and_rank f g h z hc k l hk ak hl al
  obtain ⟨m,hm,_,em⟩ := ih h z (SequentialDisjBoth.fresh k l) (.here (.disj A B) _) hf.2 hf.1
  let t := SequentialDisjBoth.rebuild (.disj A B) (BlockedDisjBoth.firstResidue A B X Y Z T)
    (BlockedDisjBoth.secondResidue A B X Y Z T) m
  have hc' : t.CutFree := by
    change t.cutCount = 0
    rw [SequentialDisjBoth.rebuild_count]
    exact hm
  refine ⟨G.atomize t,G.atomize_cutFree t hc',G.atomize_atomized t,?_⟩
  apply (G.atomize_denote t).trans
  apply (SequentialDisjBoth.rebuild_congr _ _ _ _ _ em).trans
  apply (SequentialDisjBoth.rebuild_congr _ _ _ _ _ ?_).trans
  · exact (BlockedDisjBoth.source_equation f g h z).symm
  · exact Rules.cut_congr (f:=(z.toHead.right h).denote) rfl
      (SequentialDisjBoth.fresh_congr _ _ _ _ ek el)

end CutCommutation
end DosenPetric.Reduced.Gentzen
