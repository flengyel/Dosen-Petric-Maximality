module

public import DosenPetric.GentzenSameSideLogicalFixedRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- One actual separated contraction, with explicit context identifications. -/
structure ContractionBlock (P : Type u) (U K : List (NormalForm P)) where
  C : NormalForm P
  gs : List (List (NormalForm P))
  tail : List (NormalForm P)
  upper : repeated C gs ++ tail = U
  lower : gaps gs ++ C :: tail = K

namespace ContractionBlock
variable {U K : List (NormalForm P)} (d : ContractionBlock P U K)
def route : Route K U := (copies d.C d.gs d.tail).cast d.lower d.upper
def keep : At K d.C := (At.shift (gaps d.gs) (.here d.C d.tail)).cast d.lower
def selected : List (At U d.C) := (selectedCopies d.C d.gs d.tail).map (At.cast d.upper)
theorem get_index {A : NormalForm P} (a : At U A) : (d.route.get a).index = copyIndex d.gs a.index := by
  simp only [route,Route.get_index_cast,copies_index,At.index_cast]
theorem keep_index : d.keep.index = (gaps d.gs).length := by
  simp only [keep,At.index_cast,At.index_shift,At.index,Nat.add_zero]
theorem selected_length : d.selected.length = d.gs.length := by
  simp only [selected,List.length_map,selectedCopies_length]
theorem selected_indices : d.selected.map At.index = copyOffsets d.gs := by
  simp only [selected,List.map_map,Function.comp_def,At.index_cast]
  exact selectedCopies_indices ..
theorem selected_ordered : At.Ordered d.selected := by
  apply (selectedCopies_ordered d.C d.gs d.tail).map
  intro a b h
  simpa only [At.index_cast] using h
theorem selected_iff (a : At U d.C) : a ∈ d.selected ↔ d.route.get a = d.keep := by
  have hm : a ∈ d.selected ↔ a.index ∈ copyOffsets d.gs := by
    rw [← d.selected_indices,List.mem_map]
    exact ⟨fun h => ⟨a,h,rfl⟩,fun ⟨b,hb,he⟩ => At.index_injective b a he ▸ hb⟩
  rw [hm,← copyIndex_selected]
  exact ⟨fun h => At.index_injective _ _ (by rw [d.get_index,d.keep_index]; exact h),
    fun h => by simpa only [d.get_index,d.keep_index] using congrArg At.index h⟩
def fixed {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) : At U A :=
  (fixedCopyAt d.C d.gs d.tail (z.cast d.lower.symm)
    (by simpa only [At.index_cast,d.keep_index] using hz)).cast d.upper
theorem fixed_get {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) : d.route.get (d.fixed z hz) = z := by
  apply At.index_injective
  simp only [d.get_index,fixed,At.index_cast,fixedCopyAt_index]
  exact copyIndex_fixed d.gs z.index (by simpa only [d.keep_index] using hz)
theorem fixed_unique {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index)
    (a : At U A) (ha : d.route.get a = z) : a = d.fixed z hz := by
  apply At.index_injective
  simp only [fixed,At.index_cast,fixedCopyAt_index]
  exact copyIndex_fixed_unique d.gs a.index z.index (by simpa only [d.keep_index] using hz)
    (by simpa only [d.get_index] using congrArg At.index ha)
theorem fixed_fiber {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) :
    (TraceRoute.full d.route).fiber z = [d.fixed z hz] := by
  apply TraceRoute.fiber_single
  intro a
  rw [TraceRoute.get_full,Option.some.injEq]
  exact ⟨fun h => d.fixed_unique z hz a h,fun h => h ▸ d.fixed_get z hz⟩

def applyL (hn : 2 ≤ d.gs.length) (Δ : List (NormalForm P)) (f : G P U Δ) : G P K Δ :=
  (G.contractL d.C d.gs d.tail Δ hn (f.reindex d.upper.symm rfl)).reindex d.lower rfl

def rankL (hn : 2 ≤ d.gs.length) (Δ : List (NormalForm P)) (f : G P U Δ) : Nat :=
  G.contractionRankL d.C d.gs d.tail Δ hn (f.reindex d.upper.symm rfl)

theorem rankL_keep (hn : 2 ≤ d.gs.length) (Δ : List (NormalForm P)) (f : G P U Δ) :
    (d.applyL hn Δ f).rho .left d.keep = d.rankL hn Δ f :=
  G.rho_reindex_left d.lower rfl _ _

theorem rankL_sum (hn : 2 ≤ d.gs.length) (Δ : List (NormalForm P)) (f : G P U Δ) :
    d.rankL hn Δ f = 1 + (d.selected.map (fun a => f.rho .left a)).sum :=
  G.contractionRankL_cast_eq d.C d.gs d.tail hn d.upper f

theorem rankL_fixed (hn : 2 ≤ d.gs.length) (Δ : List (NormalForm P)) (f : G P U Δ)
    {A : NormalForm P} (z : At K A) (a : At U A) (hz : z.index ≠ d.keep.index) (ha : d.route.get a = z) :
    (d.applyL hn Δ f).rho .left z = 1 + f.rho .left a :=
  contractL_cast_fixed_rank d.C d.gs d.tail hn d.lower d.upper f z a
    (by simpa only [d.keep_index] using hz) ha

theorem denoteL (hn : 2 ≤ d.gs.length) (Δ : List (NormalForm P)) (f : G P U Δ) :
    ofTerm (d.applyL hn Δ f).denote = comp (ofTerm d.route.product) (ofTerm f.denote) :=
  contractL_cast_denote d.C d.gs d.tail hn d.lower d.upper f

theorem countL (hn : 2 ≤ d.gs.length) (Δ : List (NormalForm P)) (f : G P U Δ) :
    (d.applyL hn Δ f).cutCount = f.cutCount := by
  simp only [applyL,G.count_reindex,G.cutCount]

theorem atomizedL (hn : 2 ≤ d.gs.length) (Δ : List (NormalForm P)) (f : G P U Δ) :
    (d.applyL hn Δ f).Atomized ↔ f.Atomized := by
  simp only [applyL,G.atomized_reindex,G.Atomized]

def applyR (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ U) : G P Γ K :=
  (G.contractR Γ d.C d.gs d.tail hn (f.reindex rfl d.upper.symm)).reindex rfl d.lower

def rankR (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ U) : Nat :=
  G.contractionRankR Γ d.C d.gs d.tail hn (f.reindex rfl d.upper.symm)

theorem rankR_keep (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ U) :
    (d.applyR hn Γ f).rho .right d.keep = d.rankR hn Γ f :=
  G.rho_reindex_right rfl d.lower _ _

theorem rankR_sum (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ U) :
    d.rankR hn Γ f = 1 + (d.selected.map (fun a => f.rho .right a)).sum :=
  G.contractionRankR_cast_eq d.C d.gs d.tail hn d.upper f

theorem rankR_fixed (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ U)
    {A : NormalForm P} (z : At K A) (a : At U A) (hz : z.index ≠ d.keep.index) (ha : d.route.get a = z) :
    (d.applyR hn Γ f).rho .right z = 1 + f.rho .right a :=
  contractR_cast_fixed_rank d.C d.gs d.tail hn d.lower d.upper f z a
    (by simpa only [d.keep_index] using hz) ha

theorem denoteR (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ U) :
    ofTerm (d.applyR hn Γ f).denote = comp (ofTerm f.denote) (ofTerm d.route.coproduct) :=
  contractR_cast_denote d.C d.gs d.tail hn d.lower d.upper f

theorem countR (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ U) :
    (d.applyR hn Γ f).cutCount = f.cutCount := by
  simp only [applyR,G.count_reindex,G.cutCount]

theorem atomizedR (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ U) :
    (d.applyR hn Γ f).Atomized ↔ f.Atomized := by
  simp only [applyR,G.atomized_reindex,G.Atomized]

end ContractionBlock
end DosenPetric.Reduced.Gentzen
