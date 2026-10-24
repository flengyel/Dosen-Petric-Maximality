module

public import DosenPetric.GentzenContractionFrame

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionFrame
universe u
variable {P : Type u} (d : ContractionFrame P)
variable (hSq : ∀ {A : NormalForm P} (a : At d.F A), d.c1.get (d.e0.get a) = d.e1.get (d.c0.get a))
variable (hC : d.e1.get d.keepC0 = d.xC) (hE : d.c1.get d.keepE0 = d.xE)
variable (hSep : d.xC.index ≠ d.xE.index)

include hSq hC hSep in
theorem selectedC_iff (a : At d.F d.C) : d.e0.get a ∈ d.selectedC1 ↔ a ∈ d.selectedC0 := by
  rw [d.bc1.selected_iff,d.bc0.selected_iff,hSq]
  change d.e1.get (d.c0.get a) = d.xC ↔ d.c0.get a = d.keepC0
  rw [← hC]
  exact d.be1.get_eq_iff d.keepC0 (by rw [hC]; change d.xC.index ≠ d.xE.index; exact hSep) (d.c0.get a)

include hSq hE hSep in
theorem selectedE_iff (a : At d.F d.E) : d.c0.get a ∈ d.selectedE1 ↔ a ∈ d.selectedE0 := by
  rw [d.be1.selected_iff,d.be0.selected_iff,← hSq]
  change d.c1.get (d.e0.get a) = d.xE ↔ d.e0.get a = d.keepE0
  rw [← hE]
  exact d.bc1.get_eq_iff d.keepE0 (by rw [hE]; change d.xE.index ≠ d.xC.index; exact hSep.symm) (d.e0.get a)

include hSq hC hE hSep in
theorem selectedC_transport : d.selectedC1 = d.selectedC0.map d.e0.get := by
  have ho : At.Ordered (d.selectedC0.map d.e0.get) := by
    apply List.pairwise_map.mpr
    apply d.bc0.selected_ordered.imp_of_mem
    intro a b ha hb hab
    exact d.be0.get_strict_fixed a b (d.selectedC0_parametric hSq hC hE hSep a ha)
      (d.selectedC0_parametric hSq hC hE hSep b hb) hab
  apply At.ordered_ext _ _ d.bc1.selected_ordered ho
  intro y
  constructor
  · intro hy
    let a := d.be0.fixed y (d.selectedC1_fixed hE hSep y hy)
    have he : d.e0.get a = y := d.be0.fixed_get y _
    exact List.mem_map.mpr ⟨a,(d.selectedC_iff hSq hC hSep a).mp (he.symm ▸ hy),he⟩
  · rintro h
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    exact (d.selectedC_iff hSq hC hSep a).mpr ha

include hSq hC hE hSep in
theorem selectedE_transport : d.selectedE1 = d.selectedE0.map d.c0.get := by
  have ho : At.Ordered (d.selectedE0.map d.c0.get) := by
    apply List.pairwise_map.mpr
    apply d.be0.selected_ordered.imp_of_mem
    intro a b ha hb hab
    exact d.bc0.get_strict_fixed a b (d.selectedE0_parametric hSq hC hE hSep a ha)
      (d.selectedE0_parametric hSq hC hE hSep b hb) hab
  apply At.ordered_ext _ _ d.be1.selected_ordered ho
  intro y
  constructor
  · intro hy
    let a := d.bc0.fixed y (d.selectedE1_fixed hC hSep y hy)
    have he : d.c0.get a = y := d.bc0.fixed_get y _
    exact List.mem_map.mpr ⟨a,(d.selectedE_iff hSq hE hSep a).mp (he.symm ▸ hy),he⟩
  · rintro h
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    exact (d.selectedE_iff hSq hE hSep a).mpr ha

include hSq hC hE hSep in
theorem selectedC_injective (a b : At d.F d.C) (hb : b ∈ d.selectedC0)
    (h : d.e0.get a = d.e0.get b) : a = b :=
  (d.be0.get_eq_iff b (d.selectedC0_parametric hSq hC hE hSep b hb) a).mp h

include hSq hC hE hSep in
theorem selectedE_injective (a b : At d.F d.E) (hb : b ∈ d.selectedE0)
    (h : d.c0.get a = d.c0.get b) : a = b :=
  (d.bc0.get_eq_iff b (d.selectedE0_parametric hSq hC hE hSep b hb) a).mp h

include hSq hC hSep in
theorem selectedC_final (a : At d.F d.C) (ha : a ∈ d.selectedC0) :
    d.c1.get (d.e0.get a) = d.xC ∧ d.e1.get (d.c0.get a) = d.xC := by
  have h := (d.bc1.selected_iff _).mp ((d.selectedC_iff hSq hC hSep a).mpr ha)
  exact ⟨h,(hSq a).symm.trans h⟩

include hSq hE hSep in
theorem selectedE_final (a : At d.F d.E) (ha : a ∈ d.selectedE0) :
    d.c1.get (d.e0.get a) = d.xE ∧ d.e1.get (d.c0.get a) = d.xE := by
  have h := (d.be1.selected_iff _).mp ((d.selectedE_iff hSq hE hSep a).mpr ha)
  exact ⟨(hSq a).trans h,h⟩

include hSq hC hE hSep in
theorem selectedC_singleton (a : At d.F d.C) (ha : a ∈ d.selectedC0) :
    (TraceRoute.full d.e0).fiber (d.e0.get a) = [a] := d.be0.fiber_at a (d.selectedC0_parametric hSq hC hE hSep a ha)
include hSq hC hE hSep in
theorem selectedE_singleton (a : At d.F d.E) (ha : a ∈ d.selectedE0) :
    (TraceRoute.full d.c0).fiber (d.c0.get a) = [a] := d.bc0.fiber_at a (d.selectedE0_parametric hSq hC hE hSep a ha)

include hC hSep in
theorem xC_fiber : (TraceRoute.full d.e1).fiber d.xC = [d.keepC0] := by
  rw [← hC]
  exact d.be1.fiber_at d.keepC0 (by rw [hC]; change d.xC.index ≠ d.xE.index; exact hSep)
include hE hSep in
theorem xE_fiber : (TraceRoute.full d.c1).fiber d.xE = [d.keepE0] := by
  rw [← hE]
  exact d.bc1.fiber_at d.keepE0 (by rw [hE]; change d.xE.index ≠ d.xC.index; exact hSep.symm)

def middleE {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index) : At d.FE A := d.bc1.fixed z hc
def middleC {A : NormalForm P} (z : At d.K A) (he : z.index ≠ d.xE.index) : At d.FC A := d.be1.fixed z he

theorem middleE_get {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index) : d.c1.get (d.middleE z hc) = z := d.bc1.fixed_get z hc
theorem middleC_get {A : NormalForm P} (z : At d.K A) (he : z.index ≠ d.xE.index) : d.e1.get (d.middleC z he) = z := d.be1.fixed_get z he

include hE in
theorem middleE_fixed {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) : (d.middleE z hc).index ≠ d.keepE0.index := by
  have h := congrArg At.index (d.middleE_get z hc)
  have h' := congrArg At.index hE
  rw [ContractionBlock.get_index] at h h'
  intro hi
  rw [hi,h'] at h
  exact he h.symm

include hC in
theorem middleC_fixed {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) : (d.middleC z he).index ≠ d.keepC0.index := by
  have h := congrArg At.index (d.middleC_get z he)
  have h' := congrArg At.index hC
  rw [ContractionBlock.get_index] at h h'
  intro hi
  rw [hi,h'] at h
  exact hc h.symm

def originalViaE {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) : At d.F A := d.be0.fixed (d.middleE z hc) (d.middleE_fixed hE z hc he)
def originalViaC {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) : At d.F A := d.bc0.fixed (d.middleC z he) (d.middleC_fixed hC z hc he)

theorem originalViaE_get {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) : d.e0.get (d.originalViaE hE z hc he) = d.middleE z hc := d.be0.fixed_get _ _
theorem originalViaC_get {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) : d.c0.get (d.originalViaC hC z hc he) = d.middleC z he := d.bc0.fixed_get _ _

theorem original_unique {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) (a : At d.F A) (ha : d.c1.get (d.e0.get a) = z) :
    a = d.originalViaE hE z hc he := by
  have hmid := d.bc1.fixed_unique z hc (d.e0.get a) ha
  exact d.be0.fixed_unique (d.middleE z hc) (d.middleE_fixed hE z hc he) a hmid

include hSq in
theorem original_agree {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) : d.originalViaC hC z hc he = d.originalViaE hE z hc he := by
  apply d.original_unique hE z hc he
  rw [hSq,d.originalViaC_get,d.middleC_get]

include hSq hC in
theorem other_c0_get {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) : d.c0.get (d.originalViaE hE z hc he) = d.middleC z he := by
  rw [← d.original_agree hSq hC hE z hc he,d.originalViaC_get]

include hSq hC in
/-- Complete fiber of either composite at every other final position. -/
theorem other_fiber {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) :
    (TraceRoute.full (d.e0.map d.c1.get)).fiber z = [d.originalViaE hE z hc he] ∧
    (TraceRoute.full (d.c0.map d.e1.get)).fiber z = [d.originalViaE hE z hc he] := by
  constructor <;> apply TraceRoute.fiber_single <;> intro a <;>
    rw [TraceRoute.get_full,Option.some.injEq,Route.get_map]
  · exact ⟨fun h => d.original_unique hE z hc he a h,fun h => by rw [h,d.originalViaE_get,d.middleE_get]⟩
  · exact ⟨fun h => d.original_unique hE z hc he a ((hSq a).trans h),
      fun h => by rw [h,d.other_c0_get hSq hC hE,d.middleC_get]⟩

end DosenPetric.Reduced.Gentzen.ContractionFrame
