module

public import DosenPetric.GentzenBlockedDisjFirstEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedDisjFirst
universe u
variable {P : Type u}

theorem original_descent {A B : NormalForm P} {X Y Z D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P (Z++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Y Z).keep) :
    PositionalCut.Clean h z f ((parametric A B X Y).before [A]) ∧
      PositionalCut.rank h z f ((parametric A B X Y).before [A]) <
        PositionalCut.rank h z (parent f g) (block A B X Y Z).keep := by
  have hd := (block A B X Y Z).left_cut_descent (Nat.le_refl 2) (BlockedSource.disjLLast f g)
    (((parametric A B X Y).before Z).before [.disj A B]) h z
    (by simpa only [Route.firstBlock_get] using first_get A B X Y Z) hc
  have he := BlockedSource.disjLLast_right_first_descent f g (parametric A B X Y) h z hd.1
  exact ⟨he.1,Nat.lt_trans he.2 hd.2⟩

theorem contracted_rank_gt_one {A B : NormalForm P} {X Y Z D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P (Z++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Y Z).keep) :
    1 < (parent f g).rho .left (block A B X Y Z).keep := by
  have hd := (original_descent f g h z hc).2
  have hp := f.rho_pos .left ((parametric A B X Y).before [A])
  unfold PositionalCut.rank at hd
  omega

theorem second_cutFree_atomized {A B : NormalForm P} {X Y Z D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P (Z++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Y Z).keep) :
    (SequentialDisjFirst.secondChild g).CutFree ∧ (SequentialDisjFirst.secondChild g).Atomized := by
  have ht := hc.2.1
  change (parent f g).cutCount = 0 at ht
  rw [parent,ContractionBlock.countL,BlockedSource.disjLLast_count] at ht
  have ag := ((block A B X Y Z).atomizedL (Nat.le_refl 2) _ (BlockedSource.disjLLast f g)).mp hc.2.2.2.1
  rw [BlockedSource.disjLLast_eq,BlockedSource.tailL_script,ExchangeScript.left_atomized] at ag
  refine ⟨?_,ag.2⟩
  change (BlockedSource.headL B g).cutCount = 0
  rw [BlockedSource.headL_script,ExchangeScript.left_count]
  exact (Nat.add_eq_zero_iff.mp ht).2

theorem native_child_eliminated {A B : NormalForm P} {X Y D I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (h : G P I J) (z : At J (.disj A B))
    (hf : PositionalCut.Eliminated h z f ((parametric A B X Y).before [A])) :
    PositionalCut.Eliminated h z
      (SequentialDisjFirst.child (SequentialDisjFirst.firstChild (parametric A B X Y) f))
        (.here (.disj A B) (A::(parametric A B X Y).erase)) := by
  have hs := CutCommutation.same_left_eliminated
    (SequentialLogical.principal (parametric A B X Y) A).structural _ _
    (ExchangeScript.structural_singleFiber _ _ _ (SequentialLogical.principal_selected _ A)) h z f hf
  obtain ⟨k,hk,ak,ek⟩ := hs
  refine ⟨k,hk,ak,ek.trans ?_⟩
  exact PositionalCut.congr z (.here (.disj A B) (A::(parametric A B X Y).erase)) rfl
    (SequentialDisjFirst.selected_child (parametric A B X Y) f)

end DosenPetric.Reduced.Gentzen.BlockedDisjFirst
