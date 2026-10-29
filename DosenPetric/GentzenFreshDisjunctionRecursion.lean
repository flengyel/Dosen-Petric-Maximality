module

public import DosenPetric.GentzenSequentialFrontContractionRoute

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialDisjunction
universe u
variable {P : Type u}

theorem fresh_count {F D J : List (NormalForm P)} {A B : NormalForm P}
    (k : G P F (J++A::B::D)) : (fresh k).cutCount = k.cutCount := by
  rw [fresh,G.count_reindex]
  change ((LogicalHeadRouting.components J D A B (.disj A B)).right k).cutCount = _
  rw [ExchangeScript.right_count]

theorem fresh_atomized {F D J : List (NormalForm P)} {A B : NormalForm P}
    (k : G P F (J++A::B::D)) (ak : k.Atomized) : (fresh k).Atomized := by
  apply (G.atomized_reindex ..).mpr
  exact (ExchangeScript.right_atomized _ _).mpr ak

theorem fresh_rho {F D J : List (NormalForm P)} {A B : NormalForm P}
    (k : G P F (J++A::B::D)) : (fresh k).rho .right (.here (.disj A B) (J++D)) = 1 := by
  rw [fresh,G.rho_reindex_right_at]
  have hx : (At.here (.disj A B) (J++D)).cast
      (congrArg (List.cons (.disj A B)) (At.erase_shift J D (.disj A B))).symm =
        .here (.disj A B) (At.shift J (.here (.disj A B) D)).erase := by
    apply At.index_injective
    rw [At.index_cast]
    rfl
  rw [hx]
  exact G.rho_disjR_principal ..

theorem fresh_blocked {F D J : List (NormalForm P)} {A B : NormalForm P}
    (k : G P F (J++A::B::D)) : AllBlockedAt (fresh k) .right (.here (.disj A B) (J++D)) :=
  allBlockedAt_of_leaf _ _ _ (((fresh k).rho_one_iff_leaf _ _).mp (fresh_rho k))

theorem fresh_clean {F D J I V : List (NormalForm P)} {A B : NormalForm P}
    (k : G P F (J++A::B::D)) (h : G P I V) (z : At I (.disj A B))
    (hk : k.CutFree) (ak : k.Atomized) (hh : h.CutFree) (ah : h.Atomized) (bh : AllBlockedAt h .left z) :
    PositionalCut.Clean (fresh k) (.here (.disj A B) (J++D)) h z := by
  refine ⟨?_,hh,fresh_atomized k ak,ah,fresh_blocked k,bh⟩
  change (fresh k).cutCount = 0
  rw [fresh_count]
  exact hk

theorem fresh_rank_lt {F D J I V M N : List (NormalForm P)} {A B : NormalForm P}
    (k : G P F (J++A::B::D)) (h : G P I V) (z : At I (.disj A B))
    (old : G P M N) (x : At N (.disj A B)) (hold : 1 < old.rho .right x) :
    PositionalCut.rank (fresh k) (.here (.disj A B) (J++D)) h z < PositionalCut.rank old x h z := by
  unfold PositionalCut.rank
  rw [fresh_rho]
  omega

end DosenPetric.Reduced.Gentzen.SequentialDisjunction
