module

public import DosenPetric.GentzenReducibilityObstructions
public import DosenPetric.GentzenReplacementExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ReducibilityExamples
universe u
variable {P : Type u}

def twins (l : Literal P) := G.mix (G.identity l) (G.identity l)
def first (l : Literal P) : ProofAddress (twins l) (G.identity l) :=
  ProofAddress.root.down (Premise.mix_left (G.identity l) (G.identity l))
def second (l : Literal P) : ProofAddress (twins l) (G.identity l) :=
  ProofAddress.root.down (Premise.mix_right (G.identity l) (G.identity l))

theorem distinct_sibling_nodes (l : Literal P) :
    (first l).traceAt .left (.here (.lit l) []) ≠
    (second l).traceAt .left (.here (.lit l) []) := by
  intro h
  have hp := congrArg TraceNode.address h
  cases hp

theorem sibling_clusters (l : Literal P) :
    (first l).traceAt .left (.here (.lit l) []) ∈
      ((twins l).cluster .left (.there (.here (.lit l) []))).nodes ∧
    (second l).traceAt .left (.here (.lit l) []) ∈
      ((twins l).cluster .left (.here (.lit l) [.lit l])).nodes :=
  ⟨((first l).cluster_iff_ascend .left _ _).mpr rfl,
    ((second l).cluster_iff_ascend .left _ _).mpr rfl⟩

theorem cut_surviving_rank (l : Literal P) :
    (G.identity l).rho .left (.here (.lit l) []) <
      (G.cut (G.identity l) (G.identity l)).rho .left (.here (.lit l) []) :=
  (ProofAddress.root.down (Premise.cut_left (G.identity l) (G.identity l))).ascend_rank_lt
    .left _ _ rfl (by intro h; cases h)

theorem both_signs (p : P) :
    (first (.pos p)).ascend .left (.here _ []) = some (.there (.here _ [])) ∧
    (second (.neg p)).ascend .left (.here _ []) = some (.here _ [.lit (.neg p)]) :=
  ⟨rfl,rfl⟩

theorem constant_premise_cutFree :
    (BlockedExamples.l [.conj .top .bot,.conj .top .bot,.top,.bot]).CutFree :=
  G.atomize_cutFree _ rfl

/-- A genuine Empty-variable instance of the complete root-W4 conclusion. -/
theorem constant_root_w4 :
    let d : Gentzen.SelectedLogical.Data Empty .conj := ⟨.top,.bot,[[],[]],[]⟩
    ∃ h : G Empty [.conj .top .bot] [.top],
      h.CutFree ∧
      ofTerm h.denote = ofTerm (W4.SelectedLogical.oldL d (Nat.le_refl 2) [.top]
        (BlockedExamples.l d.F)).denote ∧
      ∀ {I J : List (NormalForm Empty)} {v : G Empty I J}
        (b : ProofAddress h v) (y : At I (.conj .top .bot)),
        ReducibleL (G.identityNF (.conj .top .bot)) h b y →
        v.rho .left y < (W4.SelectedLogical.oldL d (Nat.le_refl 2) [.top]
          (BlockedExamples.l d.F)).rho .left (.here _ []) :=
  W4.SelectedLogical.two_copy_root_left [.top] .top .bot _ _ constant_premise_cutFree

end DosenPetric.Reduced.Gentzen.ReducibilityExamples
