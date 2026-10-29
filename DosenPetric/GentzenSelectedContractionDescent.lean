module

public import DosenPetric.GentzenBinaryParametricDescent
public import DosenPetric.GentzenContractionBlocks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionBlock
universe u
variable {P : Type u}

/-- Every selected contraction copy inherits the original clean invariant. -/
theorem left_cut_descent {U K Δ I J : List (NormalForm P)}
    (d : ContractionBlock P U K) (hn : 2 ≤ d.gs.length)
    (f : G P U Δ) (v : At U d.C) (h : G P I J) (z : At J d.C)
    (hv : d.route.get v = d.keep)
    (hc : PositionalCut.Clean h z (d.applyL hn Δ f) d.keep) :
    PositionalCut.Clean h z f v ∧
      PositionalCut.rank h z f v < PositionalCut.rank h z (d.applyL hn Δ f) d.keep := by
  rcases d with ⟨C,gs,T,hu,hk⟩
  cases hu
  cases hk
  let b : Upper (G.contractL C gs T Δ hn f) .left C :=
    ⟨⟨_,_,f,Premise.contractL C gs T Δ hn f⟩,v⟩
  have hb : (G.contractL C gs T Δ hn f).IsPredecessor .left
      (At.shift (gaps gs) (.here C T)) b := congrArg some hv
  exact ⟨PositionalCut.clean_right_predecessor hc b hb,
    PositionalCut.rank_right_predecessor h z _ _ b hb⟩

/-- The dual descent keeps the original right-premise proof unchanged. -/
theorem right_cut_descent {U K Γ I J : List (NormalForm P)}
    (d : ContractionBlock P U K) (hn : 2 ≤ d.gs.length)
    (f : G P Γ U) (v : At U d.C) (h : G P I J) (z : At I d.C)
    (hv : d.route.get v = d.keep)
    (hc : PositionalCut.Clean (d.applyR hn Γ f) d.keep h z) :
    PositionalCut.Clean f v h z ∧
      PositionalCut.rank f v h z < PositionalCut.rank (d.applyR hn Γ f) d.keep h z := by
  rcases d with ⟨C,gs,T,hu,hk⟩
  cases hu
  cases hk
  let b : Upper (G.contractR Γ C gs T hn f) .right C :=
    ⟨⟨_,_,f,Premise.contractR Γ C gs T hn f⟩,v⟩
  have hb : (G.contractR Γ C gs T hn f).IsPredecessor .right
      (At.shift (gaps gs) (.here C T)) b := congrArg some hv
  exact ⟨PositionalCut.clean_left_predecessor hc b hb,
    PositionalCut.rank_left_predecessor _ _ h z b hb⟩

end DosenPetric.Reduced.Gentzen.ContractionBlock
