module

public import DosenPetric.GentzenPositionalCuts
public import DosenPetric.GentzenClusterTransport

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Blockedness along the whole-formula cluster of one exact selected position. -/
def AllBlockedAt {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : Prop :=
  ∀ {U V : List (NormalForm P)} {w : G P U V} (a : ProofAddress g w)
    (z : Place s U V C), a.ascend s z = some x →
      G.LowerContraction w s z → BlockedOn s w

theorem allBlockedAt_iff_cluster {Γ Δ : List (NormalForm P)} (g : G P Γ Δ)
    (s : SequentSide) {C : NormalForm P} (x : Place s Γ Δ C) :
    AllBlockedAt g s x ↔
      ∀ {U V : List (NormalForm P)} {w : G P U V} (a : ProofAddress g w)
        (z : Place s U V C), a.traceAt s z ∈ (g.cluster s x).nodes →
          G.LowerContraction w s z → BlockedOn s w := by
  constructor
  · intro h U V w a z hz
    exact h a z ((a.cluster_iff_ascend s x z).mp hz)
  · intro h U V w a z hz
    exact h a z ((a.cluster_iff_ascend s x z).mpr hz)

theorem allBlockedAt_head_left {Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (g : G P (C :: Θ) Λ) :
    AllBlockedAt g .left (.here C Θ) ↔ AllBlockedL g := by
  rw [allBlockedAt_iff_cluster]
  constructor
  · intro h U V w a z hz
    exact h a z hz.1 hz.2
  · intro h U V w a z hz hl
    exact h a z ⟨hz,hl⟩

theorem allBlockedAt_head_right {Γ Δ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ (C :: Δ)) :
    AllBlockedAt f .right (.here C Δ) ↔ AllBlockedR f := by
  rw [allBlockedAt_iff_cluster]
  constructor
  · intro h U V w a z hz
    exact h a z hz.1 hz.2
  · intro h U V w a z hz hl
    exact h a z ⟨hz,hl⟩

/-- The same invariant at every selected predecessor, with addresses composed. -/
theorem AllBlockedAt.inherit {Γ Δ U V : List (NormalForm P)} {g : G P Γ Δ}
    {w : G P U V} {s : SequentSide} {C : NormalForm P} {x : Place s Γ Δ C}
    (h : AllBlockedAt g s x) (a : ProofAddress g w) (z : Place s U V C)
    (hz : a.ascend s z = some x) : AllBlockedAt w s z := by
  intro K L v b q hq hl
  apply h (a.append b) q _ hl
  rw [ProofAddress.ascend_append, hq]
  exact hz

/-- A fresh logical or thinning leaf has no tied lower contraction anywhere. -/
theorem allBlockedAt_of_leaf {Γ Δ : List (NormalForm P)} (g : G P Γ Δ)
    (s : SequentSide) {C : NormalForm P} (x : Place s Γ Δ C) (hx : g.Leaf s x) :
    AllBlockedAt g s x := by
  intro U V w a z hz hl
  have hr := g.rho_leaf s x hx
  cases a with
  | root =>
    have he : z = x := Option.some.inj hz
    cases he
    have hh := (g.lowerContraction_iff_arity s x).mp hl
    change g.sourceArity s x = 0 at hx
    omega
  | down a p =>
    have hp : (a.down p).path ≠ [] := by
      intro he
      have hh := congrArg List.length he
      simp only [ProofAddress.path, List.length_append, List.length_cons,
        List.length_nil] at hh
      omega
    have hlt := (a.down p).ascend_rank_lt s x z hz hp
    have hpos := w.rho_pos s z
    omega

namespace PositionalCut

def Clean {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C) : Prop :=
  f.CutFree ∧ g.CutFree ∧ f.Atomized ∧ g.Atomized ∧
    AllBlockedAt f .right x ∧ AllBlockedAt g .left y

end PositionalCut
end DosenPetric.Reduced.Gentzen
