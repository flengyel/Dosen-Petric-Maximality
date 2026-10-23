module

public import DosenPetric.GentzenSameSideExchangeRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace GapExchange.Data
variable (d : Data P)

/-- The original unique upper position above an arbitrary fixed lower position. -/
def fixed0 {A : NormalForm P} (a : At d.K0 A) (ha : a.index ≠ d.keep0.index) : At d.U0 A :=
  (fixedCopyAt d.C d.gs0 d.tail0 (a.cast d.lower0.symm)
    (by simpa only [At.index_cast,keep0_index] using ha)).cast d.upper0

theorem fixed0_get {A : NormalForm P} (a : At d.K0 A) (ha : a.index ≠ d.keep0.index) :
    d.c0.get (d.fixed0 a ha) = a := by
  apply At.index_injective
  simp only [c0_index,fixed0,At.index_cast,fixedCopyAt_index]
  exact copyIndex_fixed d.gs0 a.index (by simpa only [keep0_index] using ha)

theorem swapped_fixed {A : NormalForm P} (a : At d.K0 A) (ha : a.index ≠ d.keep0.index) :
    (d.swapLower a).index ≠ (gaps d.gs1).length := by
  intro he
  rw [swapLower_index] at he
  have hi := exchange_inverse d.loBefore.length d.X.length d.Y.length a.index
  rw [he,← d.retainedIndex,exchange_inverse] at hi
  apply ha
  exact hi.symm.trans d.keep0_index.symm

theorem fixed_canonical_image {A : NormalForm P} (a : At d.K0 A) (ha : a.index ≠ d.keep0.index) :
    (copies d.C d.gs1 d.tail1).get ((d.swapUpper (d.fixed0 a ha)).cast d.upper1.symm) =
      (d.swapLower a).cast d.lower1.symm := by
  apply At.index_injective
  simp only [copies_index,At.index_cast]
  have h := congrArg At.index ((d.square (d.fixed0 a ha)).trans (congrArg d.swapLower (d.fixed0_get a ha)))
  simpa only [c1_index] using h

/-- Complete modified singleton fiber, not just membership of its intended element. -/
theorem fixed_transport_fiber {A : NormalForm P} (a : At d.K0 A) (ha : a.index ≠ d.keep0.index) :
    (TraceRoute.full (copies d.C d.gs1 d.tail1)).fiber ((d.swapLower a).cast d.lower1.symm) =
      [(d.swapUpper (d.fixed0 a ha)).cast d.upper1.symm] := by
  have hm : (d.swapUpper (d.fixed0 a ha)).cast d.upper1.symm ∈
      (TraceRoute.full (copies d.C d.gs1 d.tail1)).fiber ((d.swapLower a).cast d.lower1.symm) :=
    (TraceRoute.fiber_correct ..).mpr ((TraceRoute.get_full ..).trans (congrArg some (d.fixed_canonical_image a ha)))
  have hx : ((d.swapLower a).cast d.lower1.symm).index ≠ (gaps d.gs1).length := by
    simpa only [At.index_cast] using d.swapped_fixed a ha
  rw [fiber_copies_fixed d.C d.gs1 d.tail1 _ hx] at hm ⊢
  rw [List.mem_singleton.mp hm]

def originalLower {A : NormalForm P} (a : At d.K1 A) : At d.K0 A :=
  a.swapBlocks d.loBefore d.Y d.X d.loAfter

theorem swapLower_original {A : NormalForm P} (a : At d.K1 A) :
    d.swapLower (d.originalLower a) = a := At.swapBlocks_inverse ..

theorem original_fixed {A : NormalForm P} (a : At d.K1 A) (ha : a.index ≠ d.keep1.index) :
    (d.originalLower a).index ≠ d.keep0.index := by
  intro he
  have hi := congrArg At.index (d.swapLower_original a)
  rw [swapLower_index,he,keep0_index,d.retainedIndex] at hi
  exact ha (hi.symm.trans d.keep1_index.symm)

end GapExchange.Data

/-- Rank counterpart of contractL_cast_denote; the supplied upper position is fixed. -/
theorem contractL_cast_fixed_rank {U K Δ : List (NormalForm P)} (C : NormalForm P)
    (gs : List (List (NormalForm P))) (Θ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (hK : gaps gs ++ C :: Θ = K) (hU : repeated C gs ++ Θ = U) (f : G P U Δ)
    {A : NormalForm P} (a : At K A) (b : At U A) (ha : a.index ≠ (gaps gs).length)
    (hb : ((copies C gs Θ).cast hK hU).get b = a) :
    ((G.contractL C gs Θ Δ hn (f.reindex hU.symm rfl)).reindex hK rfl).rho .left a =
      1 + f.rho .left b := by
  cases hK
  cases hU
  exact G.contraction_fixed_left C gs Θ Δ hn f a b ha hb

theorem contractR_cast_fixed_rank {Γ U K : List (NormalForm P)} (C : NormalForm P)
    (gs : List (List (NormalForm P))) (Θ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (hK : gaps gs ++ C :: Θ = K) (hU : repeated C gs ++ Θ = U) (f : G P Γ U)
    {A : NormalForm P} (a : At K A) (b : At U A) (ha : a.index ≠ (gaps gs).length)
    (hb : ((copies C gs Θ).cast hK hU).get b = a) :
    ((G.contractR Γ C gs Θ hn (f.reindex rfl hU.symm)).reindex rfl hK).rho .right a =
      1 + f.rho .right b := by
  cases hK
  cases hU
  exact G.contraction_fixed_right Γ C gs Θ hn f a b ha hb

namespace W1.SameSideExchange
variable (d : GapExchange.Data P) (hn : 2 ≤ d.gs0.length)

section Left
variable (Δ : List (NormalForm P)) (f : G P d.U0 Δ)

theorem fixed_innerL_rank {A : NormalForm P} (a : At d.K0 A) (ha : a.index ≠ d.keep0.index) :
    (innerL d hn Δ f).rho .left a = 1 + f.rho .left (d.fixed0 a ha) :=
  contractL_cast_fixed_rank d.C d.gs0 d.tail0 hn d.lower0 d.upper0 f a (d.fixed0 a ha)
    (by simpa only [GapExchange.Data.keep0_index] using ha) (d.fixed0_get a ha)

theorem fixed_oldL_rank {A : NormalForm P} (a : At d.K0 A) (ha : a.index ≠ d.keep0.index) :
    (oldL d hn Δ f).rho .left (d.swapLower a) = 2 + f.rho .left (d.fixed0 a ha) := by
  have h := contractL_cast_fixed_rank d.C d.gs1 d.tail1 (modifiedArity d hn) d.lower1 d.upper1
    (G.exchangeL d.upBefore d.X d.Y d.upAfter Δ f) (d.swapLower a) (d.swapUpper (d.fixed0 a ha))
    (d.swapped_fixed a ha) ((d.square _).trans (congrArg d.swapLower (d.fixed0_get a ha)))
  have he : (G.exchangeL d.upBefore d.X d.Y d.upAfter Δ f).rho .left (d.swapUpper (d.fixed0 a ha)) =
      1 + f.rho .left (d.fixed0 a ha) := G.rho_exchangeL_embedded d.upBefore d.X d.Y d.upAfter Δ f (d.fixed0 a ha)
  change (oldL d hn Δ f).rho .left (d.swapLower a) = 1 +
    (G.exchangeL d.upBefore d.X d.Y d.upAfter Δ f).rho .left (d.swapUpper (d.fixed0 a ha)) at h
  exact h.trans ((congrArg (fun n : Nat => 1+n) he).trans (by omega))

theorem fixed_newL_rank {A : NormalForm P} (a : At d.K0 A) (ha : a.index ≠ d.keep0.index) :
    (newL d hn Δ f).rho .left (d.swapLower a) = 2 + f.rho .left (d.fixed0 a ha) := by
  have h := G.rho_exchangeL_embedded d.loBefore d.X d.Y d.loAfter Δ (innerL d hn Δ f) a
  change (newL d hn Δ f).rho .left (d.swapLower a) = 1 + (innerL d hn Δ f).rho .left a at h
  rw [fixed_innerL_rank d hn Δ f a ha] at h
  omega

theorem fixed_rankL {A : NormalForm P} (a : At d.K0 A) (ha : a.index ≠ d.keep0.index) :
    (newL d hn Δ f).rho .left (d.swapLower a) = (oldL d hn Δ f).rho .left (d.swapLower a) :=
  (fixed_newL_rank d hn Δ f a ha).trans (fixed_oldL_rank d hn Δ f a ha).symm


/-- Every final fixed position is covered, using the inverse positional block swap. -/
theorem fixed_rankL_at {A : NormalForm P} (z : At d.K1 A) (hz : z.index ≠ d.keep1.index) :
    (newL d hn Δ f).rho .left z = (oldL d hn Δ f).rho .left z ∧
    (oldL d hn Δ f).rho .left z =
      2 + f.rho .left (d.fixed0 (d.originalLower z) (d.original_fixed z hz)) := by
  have ho := fixed_oldL_rank d hn Δ f (d.originalLower z) (d.original_fixed z hz)
  have hn' := fixed_newL_rank d hn Δ f (d.originalLower z) (d.original_fixed z hz)
  rw [d.swapLower_original] at ho hn'
  exact ⟨hn'.trans ho.symm,ho⟩


end Left

section Right
variable (Γ : List (NormalForm P)) (f : G P Γ d.U0)

theorem fixed_innerR_rank {A : NormalForm P} (a : At d.K0 A) (ha : a.index ≠ d.keep0.index) :
    (innerR d hn Γ f).rho .right a = 1 + f.rho .right (d.fixed0 a ha) :=
  contractR_cast_fixed_rank d.C d.gs0 d.tail0 hn d.lower0 d.upper0 f a (d.fixed0 a ha)
    (by simpa only [GapExchange.Data.keep0_index] using ha) (d.fixed0_get a ha)

theorem fixed_oldR_rank {A : NormalForm P} (a : At d.K0 A) (ha : a.index ≠ d.keep0.index) :
    (oldR d hn Γ f).rho .right (d.swapLower a) = 2 + f.rho .right (d.fixed0 a ha) := by
  have h := contractR_cast_fixed_rank d.C d.gs1 d.tail1 (modifiedArity d hn) d.lower1 d.upper1
    (G.exchangeR Γ d.upBefore d.X d.Y d.upAfter f) (d.swapLower a) (d.swapUpper (d.fixed0 a ha))
    (d.swapped_fixed a ha) ((d.square _).trans (congrArg d.swapLower (d.fixed0_get a ha)))
  have he : (G.exchangeR Γ d.upBefore d.X d.Y d.upAfter f).rho .right (d.swapUpper (d.fixed0 a ha)) =
      1 + f.rho .right (d.fixed0 a ha) := G.rho_exchangeR_embedded Γ d.upBefore d.X d.Y d.upAfter f (d.fixed0 a ha)
  change (oldR d hn Γ f).rho .right (d.swapLower a) = 1 +
    (G.exchangeR Γ d.upBefore d.X d.Y d.upAfter f).rho .right (d.swapUpper (d.fixed0 a ha)) at h
  exact h.trans ((congrArg (fun n : Nat => 1+n) he).trans (by omega))

theorem fixed_newR_rank {A : NormalForm P} (a : At d.K0 A) (ha : a.index ≠ d.keep0.index) :
    (newR d hn Γ f).rho .right (d.swapLower a) = 2 + f.rho .right (d.fixed0 a ha) := by
  have h := G.rho_exchangeR_embedded Γ d.loBefore d.X d.Y d.loAfter (innerR d hn Γ f) a
  change (newR d hn Γ f).rho .right (d.swapLower a) = 1 + (innerR d hn Γ f).rho .right a at h
  rw [fixed_innerR_rank d hn Γ f a ha] at h
  omega

theorem fixed_rankR {A : NormalForm P} (a : At d.K0 A) (ha : a.index ≠ d.keep0.index) :
    (newR d hn Γ f).rho .right (d.swapLower a) = (oldR d hn Γ f).rho .right (d.swapLower a) :=
  (fixed_newR_rank d hn Γ f a ha).trans (fixed_oldR_rank d hn Γ f a ha).symm


/-- Every final fixed position is covered, using the inverse positional block swap. -/
theorem fixed_rankR_at {A : NormalForm P} (z : At d.K1 A) (hz : z.index ≠ d.keep1.index) :
    (newR d hn Γ f).rho .right z = (oldR d hn Γ f).rho .right z ∧
    (oldR d hn Γ f).rho .right z =
      2 + f.rho .right (d.fixed0 (d.originalLower z) (d.original_fixed z hz)) := by
  have ho := fixed_oldR_rank d hn Γ f (d.originalLower z) (d.original_fixed z hz)
  have hn' := fixed_newR_rank d hn Γ f (d.originalLower z) (d.original_fixed z hz)
  rw [d.swapLower_original] at ho hn'
  exact ⟨hn'.trans ho.symm,ho⟩


end Right
end W1.SameSideExchange
end DosenPetric.Reduced.Gentzen
