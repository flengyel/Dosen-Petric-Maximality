module

public import DosenPetric.GentzenSelectionSplit
public import DosenPetric.GentzenStrictDescendants
public import DosenPetric.GentzenOtherMixRanks
public import DosenPetric.GentzenSingleMixRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {C : NormalForm P}

theorem ContractionBlock.applyL_congr {U K : List (NormalForm P)}
    {d e : ContractionBlock P U K} (h : d=e) (hn : 2 ≤ d.gs.length) (hm : 2 ≤ e.gs.length)
    (Δ : List (NormalForm P)) (f : G P U Δ) : d.applyL hn Δ f=e.applyL hm Δ f := by
  cases h
  rfl

theorem ContractionBlock.applyR_congr {U K : List (NormalForm P)}
    {d e : ContractionBlock P U K} (h : d=e) (hn : 2 ≤ d.gs.length) (hm : 2 ≤ e.gs.length)
    (Γ : List (NormalForm P)) (f : G P Γ U) : d.applyR hn Γ f=e.applyR hm Γ f := by
  cases h
  rfl

namespace MixReducer
section Left
variable {F U K Δ Λ Γ Ξ Θ Ω : List (NormalForm P)}
variable (p : ContractionSelection C (F++U) K) (hn : 2 ≤ p.arity)
variable (f : G P U Δ) (g : G P F Λ)
variable {cutLeft : G P Γ (C::Ξ)} {root : G P (C::Θ) Ω}
variable (a : ProofAddress root (p.block.applyL (p.blockArity hn) _ (G.mix f g)))
variable (hr : ReducibleL cutLeft root a p.keep)
include hr

theorem selection_left : ∃ h : G P K (Λ++Δ),
    h.CutFree ∧ ofTerm h.denote = ofTerm (p.block.applyL (p.blockArity hn) _ (G.mix f g)).denote ∧
    ∀ {I J : List (NormalForm P)} {v : G P I J} (b : ProofAddress h v) (y : At I C),
      ReducibleL cutLeft (a.replace h) ((a.inserted h).append b) y →
        v.rho .left y < (p.block.applyL (p.blockArity hn) _ (G.mix f g)).rho .left p.keep := by
  obtain ⟨hs⟩ := ContractionSelection.split_exists F U p
  cases hs with
  | left q =>
    have hq : 2 ≤ q.block.gs.length := by
      change 2 ≤ q.gs.length
      rw [q.count]
      simpa only [ContractionSelection.extend_arity] using hn
    let h := W5.SinglePremiseMix.newL q.block hq f g
    have ho : (q.extend U).block.applyL ((q.extend U).blockArity hn) _ (G.mix f g) =
        W5.SinglePremiseMix.oldL q.block hq f g :=
      ContractionBlock.applyL_congr (q.extend_block U) _ _ _ _
    have hx : (q.extend U).keep = q.block.keep.before U :=
      (q.extend_keep U).trans (congrArg (fun x => x.before U) q.keep_eq)
    have hc := hr.cutFree
    rw [ho] at hc
    have he : ofTerm h.denote = ofTerm ((q.extend U).block.applyL ((q.extend U).blockArity hn) _ (G.mix f g)).denote := by
      rw [ho]; exact W5.SinglePremiseMix.denoteL q.block hq f g
    have hk : h.rho .left (q.extend U).keep <
        ((q.extend U).block.applyL ((q.extend U).blockArity hn) _ (G.mix f g)).rho .left (q.extend U).keep := by
      rw [ho,hx]; exact W5.SinglePremiseMix.endpoint_decreasesL q.block hq f g
    refine ⟨h,(W5.SinglePremiseMix.new_cutFreeL q.block hq f g).mpr
      ((W5.SinglePremiseMix.old_cutFreeL q.block hq f g).mp hc),he,?_⟩
    exact fun b y hv => ReducibilityBoundary.strict_left a _ hr hk b y hv
  | right q =>
    have hnq : 2 ≤ q.arity := by simpa only [ContractionSelection.prepend_arity] using hn
    have hq : 2 ≤ q.block.gs.length := by change 2 ≤ q.gs.length; rw [q.count]; exact hnq
    let h := W5.OtherPremiseMix.newL q.block hq g f
    have ho : (q.prependFixed F).block.applyL ((q.prependFixed F).blockArity hn) _ (G.mix f g) =
        W5.OtherPremiseMix.oldL q.block hq g f :=
      ContractionBlock.applyL_congr (q.prepend_block hnq F) _ _ _ _
    have hx : (q.prependFixed F).keep = At.shift F q.block.keep :=
      (q.prepend_keep F).trans (congrArg (At.shift F) q.keep_eq)
    have hc := hr.cutFree
    rw [ho] at hc
    have he : ofTerm h.denote = ofTerm ((q.prependFixed F).block.applyL ((q.prependFixed F).blockArity hn) _ (G.mix f g)).denote := by
      rw [ho]; exact W5.OtherPremiseMix.denoteL q.block hq g f
    have hk : h.rho .left (q.prependFixed F).keep <
        ((q.prependFixed F).block.applyL ((q.prependFixed F).blockArity hn) _ (G.mix f g)).rho .left (q.prependFixed F).keep := by
      rw [ho,hx]; exact W5.OtherPremiseMix.endpoint_decreasesL q.block hq g f
    refine ⟨h,(W5.OtherPremiseMix.new_cutFreeL q.block hq g f).mpr
      ((W5.OtherPremiseMix.old_cutFreeL q.block hq g f).mp hc),he,?_⟩
    exact fun b y hv => ReducibilityBoundary.strict_left a _ hr hk b y hv
  | both p q =>
    have h := W5.MixedPremiseMix.addressed_left p q f g a hr
    exact ⟨_,h.1,h.2.1,h.2.2.2⟩
end Left

section Right
variable {F U K Δ Λ Γ Ξ Θ Ω : List (NormalForm P)}
variable (p : ContractionSelection C (F++U) K) (hn : 2 ≤ p.arity)
variable (f : G P Δ U) (g : G P Λ F)
variable {root : G P Γ (C::Ξ)} {cutRight : G P (C::Θ) Ω}
variable (a : ProofAddress root (p.block.applyR (p.blockArity hn) _ (G.mix f g)))
variable (hr : ReducibleR root cutRight a p.keep)
include hr

theorem selection_right : ∃ h : G P (Λ++Δ) K,
    h.CutFree ∧ ofTerm h.denote = ofTerm (p.block.applyR (p.blockArity hn) _ (G.mix f g)).denote ∧
    ∀ {I J : List (NormalForm P)} {v : G P I J} (b : ProofAddress h v) (y : At J C),
      ReducibleR (a.replace h) cutRight ((a.inserted h).append b) y →
        v.rho .right y < (p.block.applyR (p.blockArity hn) _ (G.mix f g)).rho .right p.keep := by
  obtain ⟨hs⟩ := ContractionSelection.split_exists F U p
  cases hs with
  | left q =>
    have hq : 2 ≤ q.block.gs.length := by
      change 2 ≤ q.gs.length
      rw [q.count]
      simpa only [ContractionSelection.extend_arity] using hn
    let h := W5.SinglePremiseMix.newR q.block hq f g
    have ho : (q.extend U).block.applyR ((q.extend U).blockArity hn) _ (G.mix f g) =
        W5.SinglePremiseMix.oldR q.block hq f g :=
      ContractionBlock.applyR_congr (q.extend_block U) _ _ _ _
    have hx : (q.extend U).keep = q.block.keep.before U :=
      (q.extend_keep U).trans (congrArg (fun x => x.before U) q.keep_eq)
    have hc := hr.cutFree
    rw [ho] at hc
    have he : ofTerm h.denote = ofTerm ((q.extend U).block.applyR ((q.extend U).blockArity hn) _ (G.mix f g)).denote := by
      rw [ho]; exact W5.SinglePremiseMix.denoteR q.block hq f g
    have hk : h.rho .right (q.extend U).keep <
        ((q.extend U).block.applyR ((q.extend U).blockArity hn) _ (G.mix f g)).rho .right (q.extend U).keep := by
      rw [ho,hx]; exact W5.SinglePremiseMix.endpoint_decreasesR q.block hq f g
    refine ⟨h,(W5.SinglePremiseMix.new_cutFreeR q.block hq f g).mpr
      ((W5.SinglePremiseMix.old_cutFreeR q.block hq f g).mp hc),he,?_⟩
    exact fun b y hv => ReducibilityBoundary.strict_right a _ hr hk b y hv
  | right q =>
    have hnq : 2 ≤ q.arity := by simpa only [ContractionSelection.prepend_arity] using hn
    have hq : 2 ≤ q.block.gs.length := by change 2 ≤ q.gs.length; rw [q.count]; exact hnq
    let h := W5.OtherPremiseMix.newR q.block hq g f
    have ho : (q.prependFixed F).block.applyR ((q.prependFixed F).blockArity hn) _ (G.mix f g) =
        W5.OtherPremiseMix.oldR q.block hq g f :=
      ContractionBlock.applyR_congr (q.prepend_block hnq F) _ _ _ _
    have hx : (q.prependFixed F).keep = At.shift F q.block.keep :=
      (q.prepend_keep F).trans (congrArg (At.shift F) q.keep_eq)
    have hc := hr.cutFree
    rw [ho] at hc
    have he : ofTerm h.denote = ofTerm ((q.prependFixed F).block.applyR ((q.prependFixed F).blockArity hn) _ (G.mix f g)).denote := by
      rw [ho]; exact W5.OtherPremiseMix.denoteR q.block hq g f
    have hk : h.rho .right (q.prependFixed F).keep <
        ((q.prependFixed F).block.applyR ((q.prependFixed F).blockArity hn) _ (G.mix f g)).rho .right (q.prependFixed F).keep := by
      rw [ho,hx]; exact W5.OtherPremiseMix.endpoint_decreasesR q.block hq g f
    refine ⟨h,(W5.OtherPremiseMix.new_cutFreeR q.block hq g f).mpr
      ((W5.OtherPremiseMix.old_cutFreeR q.block hq g f).mp hc),he,?_⟩
    exact fun b y hv => ReducibilityBoundary.strict_right a _ hr hk b y hv
  | both p q =>
    have h := W5.MixedPremiseMix.addressed_right p q f g a hr
    exact ⟨_,h.1,h.2.1,h.2.2.2⟩
end Right

end MixReducer
end DosenPetric.Reduced.Gentzen
