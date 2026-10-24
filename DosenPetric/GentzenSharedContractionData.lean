module

public import DosenPetric.GentzenContractionSelectionCoordinates
public import DosenPetric.GentzenRouteFiberSums

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.SharedContraction
universe u
variable {P : Type u}

/-- Two original contraction descriptions of the same intermediate context. -/
structure Data (P : Type u) where
  C : NormalForm P
  gs : List (List (NormalForm P))
  hs : List (List (NormalForm P))
  Θ : List (NormalForm P)
  Λ : List (NormalForm P)
  identify : repeated C hs ++ Λ = gaps gs ++ C :: Θ

namespace Data
variable (d : Data P)
abbrev F := repeated d.C d.gs ++ d.Θ
abbrev I := gaps d.gs ++ d.C :: d.Θ
abbrev K := gaps d.hs ++ d.C :: d.Λ
abbrev inner : ContractionBlock P d.F d.I := ⟨d.C,d.gs,d.Θ,rfl,rfl⟩
abbrev outer : ContractionBlock P d.I d.K := ⟨d.C,d.hs,d.Λ,d.identify,rfl⟩
abbrev Shared : Prop := d.inner.keep ∈ d.outer.selected

theorem inner_nonempty (hn : 2 ≤ d.gs.length) : d.gs ≠ [] := by
  intro h; rw [h] at hn; simp only [List.length_nil] at hn; omega
theorem outer_nonempty (hm : 2 ≤ d.hs.length) : d.hs ≠ [] := by
  intro h; rw [h] at hm; simp only [List.length_nil] at hm; omega

abbrev p (hn : 2 ≤ d.gs.length) := d.inner.selection (d.inner_nonempty hn)
abbrev q (hm : 2 ≤ d.hs.length) := d.outer.selection (d.outer_nonempty hm)

theorem p_block (hn : 2 ≤ d.gs.length) : (d.p hn).block = d.inner := d.inner.selection_block _
theorem q_block (hm : 2 ≤ d.hs.length) : (d.q hm).block = d.outer := d.outer.selection_block _

theorem p_route (hn : 2 ≤ d.gs.length) : (d.p hn).route = d.inner.route :=
  (d.p hn).route_eq.trans (congrArg ContractionBlock.route (d.p_block hn))
theorem q_route (hm : 2 ≤ d.hs.length) : (d.q hm).route = d.outer.route :=
  (d.q hm).route_eq.trans (congrArg ContractionBlock.route (d.q_block hm))
theorem p_keep (hn : 2 ≤ d.gs.length) : (d.p hn).keep = d.inner.keep := by
  apply At.index_injective
  rw [(d.p hn).keep_index,d.inner.keep_index]
  exact congrArg (fun gs => (gaps gs).length) (congrArg ContractionBlock.gs (d.p_block hn))
theorem q_keep (hm : 2 ≤ d.hs.length) : (d.q hm).keep = d.outer.keep := by
  apply At.index_injective
  rw [(d.q hm).keep_index,d.outer.keep_index]
  exact congrArg (fun gs => (gaps gs).length) (congrArg ContractionBlock.gs (d.q_block hm))
theorem q_selected (hm : 2 ≤ d.hs.length) : (d.q hm).selected = d.outer.selected := by
  apply At.ordered_ext _ _ (d.q hm).selected_ordered d.outer.selected_ordered
  intro a
  rw [(d.q hm).selected_iff,d.outer.selected_iff,d.q_route,d.q_keep]

theorem shared_pattern (hn : 2 ≤ d.gs.length) (hm : 2 ≤ d.hs.length) (h : d.Shared) :
    (d.p hn).keep ∈ (d.q hm).selected := by
  rw [d.p_keep,d.q_selected]
  exact h

abbrev selection (hn : 2 ≤ d.gs.length) (hm : 2 ≤ d.hs.length) (h : d.Shared) :=
  (d.p hn).fuse (d.q hm) (d.shared_pattern hn hm h)

abbrev flat (hn : 2 ≤ d.gs.length) (hm : 2 ≤ d.hs.length) (h : d.Shared) :=
  (d.selection hn hm h).block

theorem arity (hn : 2 ≤ d.gs.length) (hm : 2 ≤ d.hs.length) (h : d.Shared) :
    (d.flat hn hm h).gs.length+1 = d.gs.length+d.hs.length := by
  have hc := (d.p hn).fuse_count (d.q hm) (d.shared_pattern hn hm h)
  rw [← (d.selection hn hm h).count,← (d.p hn).count,← (d.q hm).count] at hc
  have hp : (d.p hn).gs = d.gs := congrArg ContractionBlock.gs (d.p_block hn)
  have hq : (d.q hm).gs = d.hs := congrArg ContractionBlock.gs (d.q_block hm)
  rw [hp,hq] at hc
  exact hc

theorem flat_bound (hn : 2 ≤ d.gs.length) (hm : 2 ≤ d.hs.length) (h : d.Shared) :
    2 ≤ (d.flat hn hm h).gs.length := by have he := d.arity hn hm h; omega

theorem keep (hn : 2 ≤ d.gs.length) (hm : 2 ≤ d.hs.length) (h : d.Shared) :
    (d.flat hn hm h).keep = d.outer.keep := by
  have he := (d.p hn).fuse_keep (d.q hm) (d.shared_pattern hn hm h)
  exact (d.selection hn hm h).keep_eq.symm.trans (he.trans (d.q_keep hm))

theorem square (hn : 2 ≤ d.gs.length) (hm : 2 ≤ d.hs.length) (h : d.Shared)
    {A : NormalForm P} (a : At d.F A) :
    (d.flat hn hm h).route.get a = d.outer.route.get (d.inner.route.get a) := by
  have he := (d.p hn).fuse_get (d.q hm) (d.shared_pattern hn hm h) a
  rw [(d.selection hn hm h).route_eq,d.p_route,d.q_route] at he
  exact he

theorem composite (hn : 2 ≤ d.gs.length) (hm : 2 ≤ d.hs.length) (h : d.Shared) :
    d.inner.route.map d.outer.route.get = (d.flat hn hm h).route := by
  apply Route.ext_get
  intro A a
  exact (Route.get_map ..).trans (d.square hn hm h a).symm

theorem selected_complete (hn : 2 ≤ d.gs.length) (hm : 2 ≤ d.hs.length) (h : d.Shared)
    (a : At d.F d.C) : a ∈ (d.flat hn hm h).selected ↔ d.inner.route.get a ∈ d.outer.selected := by
  rw [(d.flat hn hm h).selected_iff,d.square,d.keep,← d.outer.selected_iff]

theorem selected_originals (hn : 2 ≤ d.gs.length) (hm : 2 ≤ d.hs.length) (h : d.Shared)
    (a : At d.F d.C) :
    a ∈ (d.flat hn hm h).selected ↔ a ∈ d.inner.selected ∨
      ∃ (b : At d.I d.C) (hb : b.index ≠ d.inner.keep.index),
        b ∈ d.outer.selected ∧ a = d.inner.fixed b hb := by
  rw [d.selected_complete hn hm h a]
  constructor
  · intro ha
    by_cases he : (d.inner.route.get a).index = d.inner.keep.index
    · exact .inl ((d.inner.selected_iff a).mpr (At.index_injective _ _ he))
    · exact .inr ⟨d.inner.route.get a,he,ha,d.inner.fixed_unique _ he a rfl⟩
  · rintro (ha | ⟨b,hb,ha,rfl⟩)
    · rw [(d.inner.selected_iff a).mp ha]; exact h
    · exact (d.inner.fixed_get b hb).symm ▸ ha

theorem selected_ordered (hn : 2 ≤ d.gs.length) (hm : 2 ≤ d.hs.length) (h : d.Shared) :
    At.Ordered (d.flat hn hm h).selected := (d.flat hn hm h).selected_ordered

theorem selected_length (hn : 2 ≤ d.gs.length) (hm : 2 ≤ d.hs.length) (h : d.Shared) :
    (d.flat hn hm h).selected.length+1 = d.gs.length+d.hs.length := by
  rw [(d.flat hn hm h).selected_length]; exact d.arity hn hm h

theorem retained_fiber (hn : 2 ≤ d.gs.length) (hm : 2 ≤ d.hs.length) (h : d.Shared) :
    (TraceRoute.full (d.inner.route.map d.outer.route.get)).fiber d.outer.keep =
      (d.flat hn hm h).selected := by
  rw [d.composite hn hm h,← d.keep hn hm h,(d.flat hn hm h).selected_fiber]

def middle {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.outer.keep.index) : At d.I A :=
  d.outer.fixed z hz

theorem middle_fixed (h : d.Shared) {A : NormalForm P} (z : At d.K A)
    (hz : z.index ≠ d.outer.keep.index) : (d.middle z hz).index ≠ d.inner.keep.index := by
  have h₀ := congrArg At.index (d.outer.fixed_get z hz)
  have h₁ := congrArg At.index ((d.outer.selected_iff d.inner.keep).mp h)
  rw [ContractionBlock.get_index] at h₀ h₁
  intro he
  change (d.outer.fixed z hz).index = d.inner.keep.index at he
  rw [he,h₁] at h₀
  exact hz h₀.symm

def original (h : d.Shared) {A : NormalForm P} (z : At d.K A)
    (hz : z.index ≠ d.outer.keep.index) : At d.F A :=
  d.inner.fixed (d.middle z hz) (d.middle_fixed h z hz)

theorem original_get (h : d.Shared) {A : NormalForm P} (z : At d.K A)
    (hz : z.index ≠ d.outer.keep.index) :
    d.outer.route.get (d.inner.route.get (d.original h z hz)) = z := by
  rw [original,d.inner.fixed_get,middle,d.outer.fixed_get]

theorem original_flat (hn : 2 ≤ d.gs.length) (hm : 2 ≤ d.hs.length) (h : d.Shared)
    {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.outer.keep.index) :
    d.original h z hz = (d.flat hn hm h).fixed z (by rw [d.keep]; exact hz) := by
  apply (d.flat hn hm h).fixed_unique
  rw [d.square,d.original_get]

theorem other_fiber (hn : 2 ≤ d.gs.length) (hm : 2 ≤ d.hs.length) (h : d.Shared)
    {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.outer.keep.index) :
    (TraceRoute.full (d.inner.route.map d.outer.route.get)).fiber z = [d.original h z hz] ∧
    (TraceRoute.full (d.flat hn hm h).route).fiber z = [d.original h z hz] := by
  have he := (d.flat hn hm h).fixed_fiber z (by rw [d.keep]; exact hz)
  rw [← d.original_flat hn hm h z hz] at he
  exact ⟨(congrArg (fun w => (TraceRoute.full w).fiber z) (d.composite hn hm h)).trans he,he⟩

end Data
end DosenPetric.Reduced.Gentzen.SharedContraction
