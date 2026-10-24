module

public import DosenPetric.GentzenBlockedExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ReducibleExamples
universe u
variable {P : Type u}

def left (t : Literal P) : G P [.lit t] [.lit t] :=
  G.contractL (.lit t) [[],[]] [] [.lit t] (Nat.le_refl 2)
    (G.thinL [] [.lit t] [.lit t] (.lit t) (G.identity t))
def right (t : Literal P) : G P [.lit t] [.lit t] :=
  G.contractR [.lit t] (.lit t) [[],[]] [] (Nat.le_refl 2)
    (G.thinR [.lit t] [] [.lit t] (.lit t) (G.identity t))

theorem left_unblocked (t : Literal P) : ¬ BlockedL (left t) := by
  intro h
  have hk := h.premise_kind
  change some G.RuleKind.thinL ∈ [some .mix,some .conjR,some .exchangeL,some .conjL] at hk
  have hn : some G.RuleKind.thinL ∉ [some .mix,some .conjR,some .exchangeL,some .conjL] := by decide
  exact hn hk

theorem right_unblocked (t : Literal P) : ¬ BlockedR (right t) := by
  intro h
  have hk := h.premise_kind
  change some G.RuleKind.thinR ∈ [some .mix,some .exchangeL,some .conjR,some .disjR] at hk
  have hn : some G.RuleKind.thinR ∉ [some .mix,some .exchangeL,some .conjR,some .disjR] := by decide
  exact hn hk

theorem left_reducible (t : Literal P) :
    ReducibleL (G.identity t) (left t) ProofAddress.root (.here (.lit t) []) := by
  refine ⟨⟨rfl,rfl⟩,?_,left_unblocked t,?_⟩
  · constructor
    · exact ((left t).cluster_correct .left (.here (.lit t) []) _).mpr (.root _)
    · exact .left ..
  · intro I J v b y _ hba
    have hh := ProofAddress.proper_length hba
    change b.path.length < 0 at hh
    exact False.elim (Nat.not_lt_zero _ hh)

theorem right_reducible (t : Literal P) :
    ReducibleR (right t) (G.identity t) ProofAddress.root (.here (.lit t) []) := by
  refine ⟨⟨rfl,rfl⟩,?_,right_unblocked t,?_⟩
  · constructor
    · exact ((right t).cluster_correct .right (.here (.lit t) []) _).mpr (.root _)
    · exact .right ..
  · intro I J v b y _ hba
    have hh := ProofAddress.proper_length hba
    change b.path.length < 0 at hh
    exact False.elim (Nat.not_lt_zero _ hh)

theorem both_signs (p : P) :
    ReducibleL (G.identity (.neg p)) (left (.neg p)) ProofAddress.root (.here (.lit (.neg p)) []) ∧
    ReducibleR (right (.pos p)) (G.identity (.pos p)) ProofAddress.root (.here (.lit (.pos p)) []) :=
  ⟨left_reducible _,right_reducible _⟩

def nested (t : Literal P) : G P [.lit t] [.lit t] :=
  G.contractL (.lit t) [[],[]] [] [.lit t] (Nat.le_refl 2) (BlockedExamples.shared t)
def inner (t : Literal P) : ProofAddress (nested t) (BlockedExamples.shared t) :=
  ProofAddress.root.down (Premise.contractL (.lit t) [[],[]] [] [.lit t]
    (Nat.le_refl 2) (BlockedExamples.shared t))

theorem nested_unblocked (t : Literal P) : ¬ BlockedL (nested t) := by
  intro h
  have hk := h.premise_kind
  change some G.RuleKind.contractL ∈ [some .mix,some .conjR,some .exchangeL,some .conjL] at hk
  have hn : some G.RuleKind.contractL ∉ [some .mix,some .conjR,some .exchangeL,some .conjL] := by decide
  exact hn hk

theorem nested_inner_tied (t : Literal P) :
    (nested t).TiedRight ((inner t).traceAt .left (.here (.lit t) [.lit t])) := by
  constructor
  · apply ((nested t).cluster_correct .left (.here (.lit t) []) _).mpr
    apply FiniteTrace.Reach.step
    · exact ⟨⟨⟨_,_,BlockedExamples.shared t,
        Premise.contractL (.lit t) [[],[]] [] [.lit t] (Nat.le_refl 2) (BlockedExamples.shared t)⟩,
        .here (.lit t) [.lit t]⟩,rfl,rfl⟩
    · exact .root _
  · exact .left ..

theorem nested_inner_not_reducible (t : Literal P) :
    ¬ ReducibleL (G.identity t) (nested t) (inner t) (.here (.lit t) [.lit t]) := by
  intro h
  apply nested_unblocked t
  apply h.2.2.2 ProofAddress.root (.here (.lit t) [])
  · constructor
    · exact ((nested t).cluster_correct .left (.here (.lit t) []) _).mpr (.root _)
    · exact .left ..
  · exact ProofAddress.down_proper ..

end DosenPetric.Reduced.Gentzen.ReducibleExamples
