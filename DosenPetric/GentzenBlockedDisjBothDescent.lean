module

public import DosenPetric.GentzenBlockedDisjBothEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedDisjBoth
universe u
variable {P : Type u}

theorem first_descent {A B : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E)
    (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Y Z T).keep) :
    PositionalCut.Clean h z f ((BlockedMix.firstTag (.disj A B) X Y).before [A]) ∧
      PositionalCut.rank h z f ((BlockedMix.firstTag (.disj A B) X Y).before [A]) <
        PositionalCut.rank h z (parent f g) (block A B X Y Z T).keep := by
  have hd := (block A B X Y Z T).left_cut_descent (Nat.le_succ 2) (BlockedSource.disjLLast f g)
    (((BlockedMix.firstTag (.disj A B) X Y).before (Z++.disj A B::T)).before [.disj A B]) h z
    (by simpa only [Route.firstBlock_get] using first_get A B X Y Z T) hc
  have he := BlockedSource.disjLLast_right_first_descent f g (BlockedMix.firstTag (.disj A B) X Y) h z hd.1
  exact ⟨he.1,Nat.lt_trans he.2 hd.2⟩

theorem second_descent {A B : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E)
    (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Y Z T).keep) :
    PositionalCut.Clean h z g ((BlockedMix.firstTag (.disj A B) Z T).before [B]) ∧
      PositionalCut.rank h z g ((BlockedMix.firstTag (.disj A B) Z T).before [B]) <
        PositionalCut.rank h z (parent f g) (block A B X Y Z T).keep := by
  have hd := (block A B X Y Z T).left_cut_descent (Nat.le_succ 2) (BlockedSource.disjLLast f g)
    ((At.shift (X++.disj A B::Y) (BlockedMix.firstTag (.disj A B) Z T)).before [.disj A B]) h z
    (by simpa only [Route.firstBlock_get,Route.secondBlock_get] using second_get A B X Y Z T) hc
  have he := BlockedSource.disjLLast_right_second_descent f g (BlockedMix.firstTag (.disj A B) Z T) h z hd.1
  exact ⟨he.1,Nat.lt_trans he.2 hd.2⟩

theorem contracted_rank_gt_one {A B : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E)
    (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Y Z T).keep) :
    1 < (parent f g).rho .left (block A B X Y Z T).keep := by
  have hd := (first_descent f g h z hc).2
  have hp := f.rho_pos .left ((BlockedMix.firstTag (.disj A B) X Y).before [A])
  unfold PositionalCut.rank at hd
  omega

/-- Node-free residue transport of an eliminated original child. -/
theorem child_eliminated {F D I J : List (NormalForm P)} {C A : NormalForm P}
    (a : At F C) (f : G P (F++[A]) D) (h : G P I J) (z : At J C)
    (hf : PositionalCut.Eliminated h z f (a.before [A])) :
    ∃ k : G P ((a.erase++[A])++I) (D++z.erase), k.CutFree ∧ k.Atomized ∧
      ofTerm k.denote = ofTerm (G.cut (z.toHead.right h) ((LogicalDeletion.headBefore a [A]).left f)).denote := by
  obtain ⟨k,hk,ak,ek⟩ := hf
  refine ⟨k.reindex (congrArg (fun xs => xs++I) (a.erase_before [A])) rfl,?_,?_,?_⟩
  · exact (G.cutFree_reindex ..).mpr hk
  · exact (G.atomized_reindex ..).mpr ak
  · have he := G.reindex_congr (congrArg (fun xs => xs++I) (a.erase_before [A])) rfl ek
    rw [PositionalCut.reindex_residues h z f (a.before [A]) rfl (a.erase_before [A])] at he
    exact he

end DosenPetric.Reduced.Gentzen.BlockedDisjBoth
