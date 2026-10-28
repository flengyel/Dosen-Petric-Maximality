module

public import DosenPetric.GentzenBlockedChecks

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.AtomizationBlockedBoundary

def insertedFormula : NormalForm Empty := .disj .top .bot

def before : G Empty [.top,insertedFormula] [.top] :=
  G.thinL [.top] [] [.top] insertedFormula (G.thinL [] [] [.top] .top G.topI)

def newContraction : ProofOccurrence (G.atomize before) :=
  (G.atomize before).occurrences[4]'(by decide)

theorem new_path : newContraction.address.path = [0,0,0,0] := by decide

theorem before_blocked : AllBlockedL before := by
  intro U V w a x hx
  have hk : w.ruleKind = .contractL := by
    have hl : w.LowerContraction .left x := hx.2
    cases hl
    rfl
  have hm : a.path ∈ BlockedChecks.lowerPaths before .left := by
    apply List.mem_map.mpr
    refine ⟨ProofOccurrence.ofAddress a,?_,rfl⟩
    apply List.mem_filter.mpr
    refine ⟨a.occurrence_mem,?_⟩
    change decide (w.ruleKind = G.RuleKind.contractL) = true
    rw [hk]
    rfl
  have he : BlockedChecks.lowerPaths before .left = [] := by decide
  rw [he] at hm
  exact False.elim (List.not_mem_nil hm)

theorem new_tied : (G.atomize before).TiedRight
    (newContraction.address.traceAt .left (.there (.here .top []))) := by
  constructor
  · apply (newContraction.address.cluster_iff_ascend .left (.here .top [insertedFormula]) _).mpr
    rfl
  · exact .left ..

theorem new_unblocked : ¬ BlockedL newContraction.proof := by
  intro hb
  have hk := hb.premise_kind
  change some G.RuleKind.disjL ∈ [some .mix,some .conjR,some .exchangeL,some .conjL] at hk
  have hn : some G.RuleKind.disjL ∉ [some .mix,some .conjR,some .exchangeL,some .conjL] := by decide
  exact hn hk

/-- The existing atomization construction does not preserve the simultaneous
blocked condition, although its cut-free, equality and atomization laws hold. -/
theorem atomize_not_blocked : ¬ AllBlockedL (G.atomize before) := by
  intro hb
  exact new_unblocked (hb newContraction.address (.there (.here .top [])) new_tied)

theorem cutFree_equal_atomized :
    before.CutFree ∧ AllBlockedL before ∧ (G.atomize before).CutFree ∧
    (G.atomize before).Atomized ∧
    ofTerm (G.atomize before).denote = ofTerm before.denote ∧
    ¬ AllBlockedL (G.atomize before) :=
  ⟨rfl,before_blocked,G.atomize_cutFree before rfl,G.atomize_atomized before,
    G.atomize_denote before,atomize_not_blocked⟩

end DosenPetric.Reduced.Gentzen.AtomizationBlockedBoundary
