module

public import DosenPetric.GentzenReducibilityLogical
public import DosenPetric.GentzenBlockedExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace G
/-- A syntactic observer of the logical premise, not of its denotation. -/
def disjRightPrefix : {Γ Δ : List (NormalForm P)} → G P Γ Δ → Option Nat
  | _,_,.disjR _ Ξ _ _ _ _ => some Ξ.length
  | _,_,_ => none

def contractedDisjRightPrefix : {Γ Δ : List (NormalForm P)} → G P Γ Δ → Option Nat
  | _,_,.contractL _ _ _ _ _ f | _,_,.contractR _ _ _ _ _ f => f.disjRightPrefix
  | _,_,_ => none

theorem disjRightPrefix_reindex {Γ Δ Γ' Δ' : List (NormalForm P)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (g : G P Γ Δ) :
    (g.reindex hΓ hΔ).disjRightPrefix = g.disjRightPrefix := by cases hΓ; cases hΔ; rfl

theorem contractedDisjRightPrefix_reindex {Γ Δ Γ' Δ' : List (NormalForm P)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (g : G P Γ Δ) :
    (g.reindex hΓ hΔ).contractedDisjRightPrefix = g.contractedDisjRightPrefix := by
  cases hΓ; cases hΔ; rfl
end G

theorem BlockedR.disjRightPrefix {Γ Δ : List (NormalForm P)} {g : G P Γ Δ}
    (h : BlockedR g) : g.contractedDisjRightPrefix ∈ [none,some 0] := by
  cases h <;> simp only [BlockedSource.right2,BlockedSource.right3,
    G.contractedDisjRightPrefix,G.disjRightPrefix_reindex]
  all_goals try simp only [BlockedSource.disjLLast,G.disjRightPrefix_reindex]
  all_goals simp [G.disjRightPrefix]

namespace ReducibilityObstructions

/-- The existing right W4 replacement is terminal, whereas the blocked unary
    right pattern recognizes a head disjunction. No rank comparison is inferred
    from this syntactic separation. -/
theorem terminal_right_w4_unblocked (d : Gentzen.SelectedLogical.Data P .disj)
    (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ d.F) :
    ¬ BlockedR (W4.SelectedLogical.newR d hn Γ f) := by
  intro hb
  have hp := hb.disjRightPrefix
  have he : (W4.SelectedLogical.newR d hn Γ f).contractedDisjRightPrefix =
      some d.s.I.length := by
    unfold W4.SelectedLogical.newR ContractionBlock.applyR
    rw [G.contractedDisjRightPrefix_reindex]
    change ((W4.SelectedLogical.middleR d hn Γ f).reindex rfl d.lastSource.symm).disjRightPrefix = _
    rw [G.disjRightPrefix_reindex]
    rfl
  rw [he] at hp
  have hl : 0 < d.s.I.length := by
    change 0 < (gaps d.gs++d.C::d.Θ).length
    simp only [List.length_append,List.length_cons]
    omega
  simp only [List.mem_cons,List.not_mem_nil,or_false,Option.some_ne_none,
    Option.some.injEq,false_or] at hp
  omega

def freshBothContraction : G Empty [.disj .top .bot] [.top,.top] :=
  G.contractL (.disj .top .bot) [[],[],[]] [] [.top,.top]
    (Nat.le_succ 2) BlockedExamples.freshBoth

theorem freshBoth_unblocked : ¬ BlockedL freshBothContraction := by
  intro hb
  have h := hb.premise_kind
  simp [freshBothContraction,G.contractedPremiseKind,G.ruleKind,BlockedExamples.freshBoth] at h

theorem splitMix_blocked (t : Literal P) :
    BlockedL (G.contractL (.lit t) [[],[]] [] [.lit t,.lit t]
      (Nat.le_refl 2) (BlockedExamples.splitMix t)) :=
  .gammaMix (.lit t) [] [] [] [] [.lit t] [.lit t] (G.identity t) (G.identity t)

end ReducibilityObstructions
end DosenPetric.Reduced.Gentzen
