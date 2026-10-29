module

public import DosenPetric.GentzenBlockedDisjunctionEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedDisjunction
universe u
variable {P : Type u}

theorem original_descent {A B : NormalForm P} {F X Y I J : List (NormalForm P)}
    (f : G P F (A::B::(X++.disj A B::Y))) (h : G P I J) (z : At I (.disj A B))
    (hc : PositionalCut.Clean (parent f) (block A B X Y).keep h z) :
    PositionalCut.Clean f (.there (.there (parametric A B X Y))) h z ∧
      PositionalCut.rank f (.there (.there (parametric A B X Y))) h z <
        PositionalCut.rank (parent f) (block A B X Y).keep h z := by
  have hd := (block A B X Y).right_cut_descent (Nat.le_refl 2)
    (G.disjR F [] (X++.disj A B::Y) A B f) (.there (parametric A B X Y)) h z
    (parametric_get A B X Y) hc
  have he := PositionalCut.same_disjR_tail_descent (F:=[]) f (parametric A B X Y) h z hd.1
  exact ⟨he.1,Nat.lt_trans he.2 hd.2⟩

theorem contracted_rank_gt_one {A B : NormalForm P} {F X Y I J : List (NormalForm P)}
    (f : G P F (A::B::(X++.disj A B::Y))) (h : G P I J) (z : At I (.disj A B))
    (hc : PositionalCut.Clean (parent f) (block A B X Y).keep h z) :
    1 < (parent f).rho .right (block A B X Y).keep := by
  have hd := (original_descent f h z hc).2
  have hp := f.rho_pos .right (.there (.there (parametric A B X Y)))
  unfold PositionalCut.rank at hd
  omega

theorem native_child_eliminated {A B : NormalForm P} {F X Y I J : List (NormalForm P)}
    (f : G P F (A::B::(X++.disj A B::Y))) (h : G P I J) (z : At I (.disj A B))
    (hf : PositionalCut.Eliminated f (.there (.there (parametric A B X Y))) h z) :
    PositionalCut.Eliminated (nativeChild f) (.here (.disj A B) (A::B::(parametric A B X Y).erase)) h z := by
  have hs : (LogicalDeletion.headUnder [] [A,B] (parametric A B X Y)).get
      (.there (.there (parametric A B X Y))) = .here (.disj A B) (A::B::(parametric A B X Y).erase) := by
    simpa only [At.shift,List.nil_append,List.cons_append] using
      LogicalDeletion.headUnder_selected [] [A,B] (parametric A B X Y)
  exact CutCommutation.same_right_eliminated
    (LogicalDeletion.headUnder [] [A,B] (parametric A B X Y)).structural _ _
      (ExchangeScript.structural_singleFiber _ _ _ hs) f h z hf

end DosenPetric.Reduced.Gentzen.BlockedDisjunction
