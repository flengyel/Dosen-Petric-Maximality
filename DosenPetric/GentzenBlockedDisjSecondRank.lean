module

public import DosenPetric.GentzenBlockedDisjSecondDescent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SequentialDisjSecond

theorem fresh_congr {F U D E I R : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::F) D) (k k' : G P (B::(U++I)) (E++R))
    (he : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (fresh f k).denote = ofTerm (fresh f k').denote :=
  Rules.disjLeft_congr rfl he

end SequentialDisjSecond
namespace BlockedDisjSecond

theorem fresh_clean_and_rank {A B : NormalForm P} {X Z T D E I J : List (NormalForm P)}
    (f : G P (X++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Z T).keep)
    (k : G P (B::((parametric A B Z T).erase++I)) (E++z.erase)) (hk : k.CutFree) (ak : k.Atomized) :
    PositionalCut.Clean h z (SequentialDisjSecond.fresh (SequentialDisjSecond.firstChild f) k)
      (.here (.disj A B) (X++((parametric A B Z T).erase++I))) ∧
      PositionalCut.rank h z (SequentialDisjSecond.fresh (SequentialDisjSecond.firstChild f) k)
        (.here (.disj A B) (X++((parametric A B Z T).erase++I))) <
          PositionalCut.rank h z (parent f g) (block A B X Z T).keep := by
  obtain ⟨hf,af⟩ := first_cutFree_atomized f g h z hc
  refine ⟨⟨hc.1,(G.disjL_cutFree _ _).mpr ⟨hf,hk⟩,hc.2.2.1,⟨af,ak⟩,
    hc.2.2.2.2.1,G.disjL_principal_blocked (SequentialDisjSecond.firstChild f) k⟩,?_⟩
  exact PositionalCut.rank_fresh_disjL_lt h z (parent f g) _ (contracted_rank_gt_one f g h z hc)
    (SequentialDisjSecond.firstChild f) k

end BlockedDisjSecond
namespace CutCommutation

theorem blockedL_disjunctionSecond_rank_step {A B : NormalForm P} {X Z T D E I J : List (NormalForm P)}
    (f : G P (X++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (BlockedDisjSecond.parent f g) (BlockedDisjSecond.block A B X Z T).keep)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L (.disj A B))
      (d : G P M N) (w : At M (.disj A B)),
      PositionalCut.rank b v d w <
        PositionalCut.rank h z (BlockedDisjSecond.parent f g) (BlockedDisjSecond.block A B X Z T).keep →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (BlockedDisjSecond.parent f g) (BlockedDisjSecond.block A B X Z T).keep := by
  have hd := BlockedDisjSecond.original_descent f g h z hc
  have hs := ih h z g ((BlockedDisjSecond.parametric A B Z T).before [B]) hd.2 hd.1
  obtain ⟨k,hk,ak,ek⟩ := BlockedDisjSecond.native_child_eliminated g h z hs
  have hf := BlockedDisjSecond.fresh_clean_and_rank f g h z hc k hk ak
  obtain ⟨l,hl,_,el⟩ := ih h z
    (SequentialDisjSecond.fresh (SequentialDisjSecond.firstChild f) k) (.here (.disj A B) _) hf.2 hf.1
  let t := SequentialDisjSecond.rebuild A B (BlockedDisjSecond.residue A B X Z T) l
  have ht : t.CutFree := by
    change t.cutCount = 0
    rw [SequentialDisjSecond.rebuild_count]
    exact hl
  refine ⟨G.atomize t,G.atomize_cutFree t ht,G.atomize_atomized t,?_⟩
  apply (G.atomize_denote t).trans
  apply (SequentialDisjSecond.rebuild_congr _ _ _ _ _ el).trans
  apply (SequentialDisjSecond.rebuild_congr _ _ _ _ _ ?_).trans
  · exact (BlockedDisjSecond.source_equation f g h z).symm
  · exact Rules.cut_congr rfl (SequentialDisjSecond.fresh_congr _ _ _ ek)

end CutCommutation
end DosenPetric.Reduced.Gentzen
