module

public import DosenPetric.GentzenBlockedConjunctionEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedConjunction
universe u
variable {P : Type u}

theorem original_descent {A B : NormalForm P} {X Y D I J : List (NormalForm P)}
    (f : G P ((X++.conj A B::Y)++[A,B]) D) (h : G P I J) (z : At J (.conj A B))
    (hc : PositionalCut.Clean h z (parent f) (block A B X Y).keep) :
    PositionalCut.Clean h z f ((parametric A B X Y).before [A,B]) ∧
      PositionalCut.rank h z f ((parametric A B X Y).before [A,B]) <
        PositionalCut.rank h z (parent f) (block A B X Y).keep := by
  have hd := (block A B X Y).left_cut_descent (Nat.le_refl 2)
    (BlockedSource.conjLLast _ D A B f) ((parametric A B X Y).before [.conj A B]) h z
    (by simpa only [Route.firstBlock_get] using first_get A B X Y) hc
  have he := PositionalCut.same_conjL_before_descent h z f (parametric A B X Y) hd.1
  exact ⟨he.1,Nat.lt_trans he.2 hd.2⟩

theorem contracted_rank_gt_one {A B : NormalForm P} {X Y D I J : List (NormalForm P)}
    (f : G P ((X++.conj A B::Y)++[A,B]) D) (h : G P I J) (z : At J (.conj A B))
    (hc : PositionalCut.Clean h z (parent f) (block A B X Y).keep) :
    1 < (parent f).rho .left (block A B X Y).keep := by
  have hd := (original_descent f h z hc).2
  have hp := f.rho_pos .left ((parametric A B X Y).before [A,B])
  unfold PositionalCut.rank at hd
  omega

theorem native_child_eliminated {A B : NormalForm P} {X Y D I J : List (NormalForm P)}
    (f : G P ((X++.conj A B::Y)++[A,B]) D) (h : G P I J) (z : At J (.conj A B))
    (hf : PositionalCut.Eliminated h z f ((parametric A B X Y).before [A,B])) :
    PositionalCut.Eliminated h z (nativeChild f) (.here (.conj A B) (A::B::(parametric A B X Y).erase)) :=
  CutCommutation.same_left_eliminated (SequentialLogical.components (parametric A B X Y) A B).structural
    _ _ (ExchangeScript.structural_singleFiber _ _ _ (SequentialLogical.components_selected _ A B)) h z f hf

theorem fresh_clean_and_rank {A B : NormalForm P} {X Y D I J : List (NormalForm P)}
    (f : G P ((X++.conj A B::Y)++[A,B]) D) (h : G P I J) (z : At J (.conj A B))
    (hc : PositionalCut.Clean h z (parent f) (block A B X Y).keep)
    (k : G P ((A::B::(parametric A B X Y).erase)++I) (D++z.erase)) (hk : k.CutFree) (ak : k.Atomized) :
    PositionalCut.Clean h z (SequentialConjunction.fresh k) (.here (.conj A B) ((parametric A B X Y).erase++I)) ∧
      PositionalCut.rank h z (SequentialConjunction.fresh k) (.here (.conj A B) ((parametric A B X Y).erase++I)) <
        PositionalCut.rank h z (parent f) (block A B X Y).keep := by
  exact ⟨PositionalCut.clean_fresh_conjL (F:=[]) (U:=(parametric A B X Y).erase++I)
      h z k hc.1 hc.2.2.1 hc.2.2.2.2.1 hk ak,
    PositionalCut.rank_fresh_conjL_lt (F:=[]) (U:=(parametric A B X Y).erase++I)
      h z (parent f) _ (contracted_rank_gt_one f h z hc) k⟩

end DosenPetric.Reduced.Gentzen.BlockedConjunction
