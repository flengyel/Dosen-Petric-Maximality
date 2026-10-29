module

public import DosenPetric.GentzenBlockedDisjSecondEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedDisjSecond
universe u
variable {P : Type u}

theorem original_descent {A B : NormalForm P} {X Z T D E I J : List (NormalForm P)}
    (f : G P (X++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Z T).keep) :
    PositionalCut.Clean h z g ((parametric A B Z T).before [B]) ∧
      PositionalCut.rank h z g ((parametric A B Z T).before [B]) <
        PositionalCut.rank h z (parent f g) (block A B X Z T).keep := by
  have hd := (block A B X Z T).left_cut_descent (Nat.le_refl 2) (BlockedSource.disjLLast f g)
    ((At.shift X (parametric A B Z T)).before [.disj A B]) h z
    (by simpa only [Route.firstBlock_get] using first_get A B X Z T) hc
  have he := BlockedSource.disjLLast_right_second_descent f g (parametric A B Z T) h z hd.1
  exact ⟨he.1,Nat.lt_trans he.2 hd.2⟩

theorem contracted_rank_gt_one {A B : NormalForm P} {X Z T D E I J : List (NormalForm P)}
    (f : G P (X++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Z T).keep) :
    1 < (parent f g).rho .left (block A B X Z T).keep := by
  have hd := (original_descent f g h z hc).2
  have hp := g.rho_pos .left ((parametric A B Z T).before [B])
  unfold PositionalCut.rank at hd
  omega

theorem first_cutFree_atomized {A B : NormalForm P} {X Z T D E I J : List (NormalForm P)}
    (f : G P (X++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Z T).keep) :
    (SequentialDisjSecond.firstChild f).CutFree ∧ (SequentialDisjSecond.firstChild f).Atomized := by
  have ht := hc.2.1
  change (parent f g).cutCount = 0 at ht
  rw [parent,ContractionBlock.countL,BlockedSource.disjLLast_count] at ht
  have af := ((block A B X Z T).atomizedL (Nat.le_refl 2) _ (BlockedSource.disjLLast f g)).mp hc.2.2.2.1
  rw [BlockedSource.disjLLast_eq,BlockedSource.tailL_script,ExchangeScript.left_atomized] at af
  refine ⟨?_,af.1⟩
  change (BlockedSource.headL A f).cutCount = 0
  rw [BlockedSource.headL_script,ExchangeScript.left_count]
  exact (Nat.add_eq_zero_iff.mp ht).1

theorem native_child_eliminated {A B : NormalForm P} {Z T E I J : List (NormalForm P)}
    (g : G P ((Z++.disj A B::T)++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (hg : PositionalCut.Eliminated h z g ((parametric A B Z T).before [B])) :
    PositionalCut.Eliminated h z
      (SequentialDisjSecond.child (SequentialDisjSecond.secondChild (parametric A B Z T) g))
        (.here (.disj A B) (B::(parametric A B Z T).erase)) := by
  have hs := CutCommutation.same_left_eliminated
    (SequentialLogical.principal (parametric A B Z T) B).structural _ _
    (ExchangeScript.structural_singleFiber _ _ _ (SequentialLogical.principal_selected _ B)) h z g hg
  obtain ⟨k,hk,ak,ek⟩ := hs
  refine ⟨k,hk,ak,ek.trans ?_⟩
  exact PositionalCut.congr z (.here (.disj A B) (B::(parametric A B Z T).erase)) rfl
    (SequentialDisjSecond.selected_child (parametric A B Z T) g)

end DosenPetric.Reduced.Gentzen.BlockedDisjSecond
