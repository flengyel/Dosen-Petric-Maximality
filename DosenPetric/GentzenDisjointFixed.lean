module

public import DosenPetric.GentzenDisjointTransport

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionBlock
variable {U K : List (NormalForm P)} (d : ContractionBlock P U K)
theorem fiber_at {A : NormalForm P} (a : At U A) (ha : (d.route.get a).index ≠ d.keep.index) :
    (TraceRoute.full d.route).fiber (d.route.get a) = [a] := by
  rw [d.fixed_fiber _ ha,← d.fixed_unique _ ha a rfl]
end ContractionBlock

namespace Disjoint.Data
variable (d : Data P)

theorem selectedC_singleton (a : At d.F d.C) (ha : a ∈ d.selectedC0) :
    (TraceRoute.full d.e0).fiber (d.e0.get a) = [a] := d.be0.fiber_at a (d.selectedC0_parametric a ha)
theorem selectedE_singleton (a : At d.F d.E) (ha : a ∈ d.selectedE0) :
    (TraceRoute.full d.c0).fiber (d.c0.get a) = [a] := d.bc0.fiber_at a (d.selectedE0_parametric a ha)

theorem xC_fiber : (TraceRoute.full d.e1).fiber d.xC = [d.keepC0] := by
  rw [← d.e1_keepC0]
  exact d.be1.fiber_at d.keepC0 (by rw [d.e1_keepC0]; change d.xC.index ≠ d.xE.index; have h := d.retained_order; omega)
theorem xE_fiber : (TraceRoute.full d.c1).fiber d.xE = [d.keepE0] := by
  rw [← d.c1_keepE0]
  exact d.bc1.fiber_at d.keepE0 (by rw [d.c1_keepE0]; change d.xE.index ≠ d.xC.index; have h := d.retained_order; omega)

def middleE {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index) : At d.FE A := d.bc1.fixed z hc
def middleC {A : NormalForm P} (z : At d.K A) (he : z.index ≠ d.xE.index) : At d.FC A := d.be1.fixed z he

theorem middleE_get {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index) : d.c1.get (d.middleE z hc) = z := d.bc1.fixed_get z hc
theorem middleC_get {A : NormalForm P} (z : At d.K A) (he : z.index ≠ d.xE.index) : d.e1.get (d.middleC z he) = z := d.be1.fixed_get z he

theorem middleE_fixed {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) : (d.middleE z hc).index ≠ d.keepE0.index := by
  have h := congrArg At.index (d.middleE_get z hc)
  have h' := congrArg At.index d.c1_keepE0
  rw [ContractionBlock.get_index] at h h'
  intro hi
  rw [hi,h'] at h
  exact he h.symm

theorem middleC_fixed {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) : (d.middleC z he).index ≠ d.keepC0.index := by
  have h := congrArg At.index (d.middleC_get z he)
  have h' := congrArg At.index d.e1_keepC0
  rw [ContractionBlock.get_index] at h h'
  intro hi
  rw [hi,h'] at h
  exact hc h.symm

def originalViaE {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) : At d.F A := d.be0.fixed (d.middleE z hc) (d.middleE_fixed z hc he)
def originalViaC {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) : At d.F A := d.bc0.fixed (d.middleC z he) (d.middleC_fixed z hc he)

theorem originalViaE_get {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) : d.e0.get (d.originalViaE z hc he) = d.middleE z hc := d.be0.fixed_get _ _
theorem originalViaC_get {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) : d.c0.get (d.originalViaC z hc he) = d.middleC z he := d.bc0.fixed_get _ _

theorem original_unique {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) (a : At d.F A) (ha : d.c1.get (d.e0.get a) = z) :
    a = d.originalViaE z hc he := by
  have hmid := d.bc1.fixed_unique z hc (d.e0.get a) ha
  exact d.be0.fixed_unique (d.middleE z hc) (d.middleE_fixed z hc he) a hmid

theorem original_agree {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) : d.originalViaC z hc he = d.originalViaE z hc he := by
  apply d.original_unique z hc he
  rw [d.square,d.originalViaC_get,d.middleC_get]

theorem other_c0_get {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) : d.c0.get (d.originalViaE z hc he) = d.middleC z he := by
  rw [← d.original_agree z hc he,d.originalViaC_get]

/-- Complete fiber of either composite at every other final position. -/
theorem other_fiber {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) :
    (TraceRoute.full (d.e0.map d.c1.get)).fiber z = [d.originalViaE z hc he] ∧
    (TraceRoute.full (d.c0.map d.e1.get)).fiber z = [d.originalViaE z hc he] := by
  constructor <;> apply TraceRoute.fiber_single <;> intro a <;>
    rw [TraceRoute.get_full,Option.some.injEq,Route.get_map]
  · exact ⟨fun h => d.original_unique z hc he a h,fun h => by rw [h,d.originalViaE_get,d.middleE_get]⟩
  · exact ⟨fun h => d.original_unique z hc he a ((d.square a).trans h),
      fun h => by rw [h,d.other_c0_get,d.middleC_get]⟩

end Disjoint.Data
end DosenPetric.Reduced.Gentzen
