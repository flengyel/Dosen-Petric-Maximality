module

public import DosenPetric.GentzenBlockedDisjFirstDescent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SequentialDisjFirst

theorem fresh_congr {F U D E I R : List (NormalForm P)} {A B : NormalForm P}
    (k k' : G P (A::(F++I)) (D++R)) (g : G P (B::U) E)
    (he : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (fresh k g).denote = ofTerm (fresh k' g).denote :=
  Rules.disjLeft_congr he rfl

end SequentialDisjFirst
namespace BlockedDisjFirst

theorem fresh_clean_and_rank {A B : NormalForm P} {X Y Z D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P (Z++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Y Z).keep)
    (k : G P (A::((parametric A B X Y).erase++I)) (D++z.erase)) (hk : k.CutFree) (ak : k.Atomized) :
    PositionalCut.Clean h z (SequentialDisjFirst.fresh k (SequentialDisjFirst.secondChild g))
      (.here (.disj A B) (((parametric A B X Y).erase++I)++Z)) ∧
      PositionalCut.rank h z (SequentialDisjFirst.fresh k (SequentialDisjFirst.secondChild g))
        (.here (.disj A B) (((parametric A B X Y).erase++I)++Z)) <
          PositionalCut.rank h z (parent f g) (block A B X Y Z).keep := by
  obtain ⟨hg,ag⟩ := second_cutFree_atomized f g h z hc
  refine ⟨⟨hc.1,(G.disjL_cutFree _ _).mpr ⟨hk,hg⟩,hc.2.2.1,⟨ak,ag⟩,
    hc.2.2.2.2.1,G.disjL_principal_blocked k (SequentialDisjFirst.secondChild g)⟩,?_⟩
  exact PositionalCut.rank_fresh_disjL_lt h z (parent f g) _ (contracted_rank_gt_one f g h z hc)
    k (SequentialDisjFirst.secondChild g)

end BlockedDisjFirst
namespace CutCommutation

theorem blockedL_disjunctionFirst_rank_step {A B : NormalForm P} {X Y Z D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P (Z++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (BlockedDisjFirst.parent f g) (BlockedDisjFirst.block A B X Y Z).keep)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L (.disj A B))
      (d : G P M N) (w : At M (.disj A B)),
      PositionalCut.rank b v d w <
        PositionalCut.rank h z (BlockedDisjFirst.parent f g) (BlockedDisjFirst.block A B X Y Z).keep →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (BlockedDisjFirst.parent f g) (BlockedDisjFirst.block A B X Y Z).keep := by
  have hd := BlockedDisjFirst.original_descent f g h z hc
  have hs := ih h z f ((BlockedDisjFirst.parametric A B X Y).before [A]) hd.2 hd.1
  obtain ⟨k,hk,ak,ek⟩ := BlockedDisjFirst.native_child_eliminated f h z hs
  have hf := BlockedDisjFirst.fresh_clean_and_rank f g h z hc k hk ak
  obtain ⟨l,hl,_,el⟩ := ih h z
    (SequentialDisjFirst.fresh k (SequentialDisjFirst.secondChild g)) (.here (.disj A B) _) hf.2 hf.1
  let t := SequentialDisjFirst.rebuild A B (BlockedDisjFirst.residue A B X Y Z) l
  have ht : t.CutFree := by
    change t.cutCount = 0
    rw [SequentialDisjFirst.rebuild_count]
    exact hl
  refine ⟨G.atomize t,G.atomize_cutFree t ht,G.atomize_atomized t,?_⟩
  apply (G.atomize_denote t).trans
  apply (SequentialDisjFirst.rebuild_congr _ _ _ _ _ el).trans
  apply (SequentialDisjFirst.rebuild_congr _ _ _ _ _ ?_).trans
  · exact (BlockedDisjFirst.source_equation f g h z).symm
  · exact Rules.cut_congr rfl (SequentialDisjFirst.fresh_congr _ _ _ ek)

end CutCommutation
end DosenPetric.Reduced.Gentzen
