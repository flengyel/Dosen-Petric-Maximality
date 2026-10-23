module

public import DosenPetric.GentzenDisjointPositions

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace ContractionBlock
variable {U K : List (NormalForm P)} (d : ContractionBlock P U K)
theorem get_eq_iff {A : NormalForm P} (b : At U A) (hb : (d.route.get b).index ≠ d.keep.index) (a : At U A) :
    d.route.get a = d.route.get b ↔ a = b := by
  constructor
  · intro h
    exact (d.fixed_unique _ hb a h).trans (d.fixed_unique _ hb b rfl).symm
  · intro h; cases h; rfl
end ContractionBlock

namespace Disjoint.Data
variable (d : Data P)

theorem selectedC_iff (a : At d.F d.C) : d.e0.get a ∈ d.selectedC1 ↔ a ∈ d.selectedC0 := by
  rw [d.bc1.selected_iff,d.bc0.selected_iff,d.square]
  change d.e1.get (d.c0.get a) = d.xC ↔ d.c0.get a = d.keepC0
  rw [← d.e1_keepC0]
  exact d.be1.get_eq_iff d.keepC0 (by rw [d.e1_keepC0]; change d.xC.index ≠ d.xE.index; have h := d.retained_order; omega) (d.c0.get a)

theorem selectedE_iff (a : At d.F d.E) : d.c0.get a ∈ d.selectedE1 ↔ a ∈ d.selectedE0 := by
  rw [d.be1.selected_iff,d.be0.selected_iff,← d.square]
  change d.c1.get (d.e0.get a) = d.xE ↔ d.e0.get a = d.keepE0
  rw [← d.c1_keepE0]
  exact d.bc1.get_eq_iff d.keepE0 (by rw [d.c1_keepE0]; change d.xE.index ≠ d.xC.index; have h := d.retained_order; omega) (d.e0.get a)

theorem selectedC_transport : d.selectedC1 = d.selectedC0.map d.e0.get := by
  have ho : At.Ordered (d.selectedC0.map d.e0.get) := by
    apply List.pairwise_map.mpr
    apply d.bc0.selected_ordered.imp_of_mem
    intro a b ha hb hab
    rw [d.e0_index,d.e0_index]
    exact splice_outside_strict _ _ _ _ _ _ (d.selectedC0_outside a ha) (d.selectedC0_outside b hb) hab
  apply At.ordered_ext _ _ d.bc1.selected_ordered ho
  intro y
  constructor
  · intro hy
    let a := d.be0.fixed y (d.selectedC1_fixed y hy)
    have he : d.e0.get a = y := d.be0.fixed_get y _
    exact List.mem_map.mpr ⟨a,(d.selectedC_iff a).mp (he.symm ▸ hy),he⟩
  · rintro h
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    exact (d.selectedC_iff a).mpr ha

theorem selectedE_transport : d.selectedE1 = d.selectedE0.map d.c0.get := by
  have ho : At.Ordered (d.selectedE0.map d.c0.get) := by
    apply List.pairwise_map.mpr
    apply d.be0.selected_ordered.imp_of_mem
    intro a b ha hb hab
    have h₁ := d.selectedE0_inside a ha
    have h₂ := d.selectedE0_inside b hb
    rw [d.c0_inside a h₁.1 h₁.2,d.c0_inside b h₂.1 h₂.2]
    omega
  apply At.ordered_ext _ _ d.be1.selected_ordered ho
  intro y
  constructor
  · intro hy
    let a := d.bc0.fixed y (d.selectedE1_fixed y hy)
    have he : d.c0.get a = y := d.bc0.fixed_get y _
    exact List.mem_map.mpr ⟨a,(d.selectedE_iff a).mp (he.symm ▸ hy),he⟩
  · rintro h
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    exact (d.selectedE_iff a).mpr ha

theorem selectedC0_length : d.selectedC0.length = d.outer0.length := d.bc0.selected_length
theorem selectedC1_length : d.selectedC1.length = d.outer0.length := d.bc1.selected_length.trans d.countC
theorem selectedE0_length : d.selectedE0.length = d.es.length := d.be0.selected_length
theorem selectedE1_length : d.selectedE1.length = d.es.length := d.be1.selected_length

theorem selectedC_injective (a b : At d.F d.C) (hb : b ∈ d.selectedC0)
    (h : d.e0.get a = d.e0.get b) : a = b :=
  (d.be0.get_eq_iff b (d.selectedC0_parametric b hb) a).mp h

theorem selectedE_injective (a b : At d.F d.E) (hb : b ∈ d.selectedE0)
    (h : d.c0.get a = d.c0.get b) : a = b :=
  (d.bc0.get_eq_iff b (d.selectedE0_parametric b hb) a).mp h

theorem selectedC_final (a : At d.F d.C) (ha : a ∈ d.selectedC0) :
    d.c1.get (d.e0.get a) = d.xC ∧ d.e1.get (d.c0.get a) = d.xC := by
  have h := (d.bc1.selected_iff _).mp ((d.selectedC_iff a).mpr ha)
  exact ⟨h,(d.square a).symm.trans h⟩

theorem selectedE_final (a : At d.F d.E) (ha : a ∈ d.selectedE0) :
    d.c1.get (d.e0.get a) = d.xE ∧ d.e1.get (d.c0.get a) = d.xE := by
  have h := (d.be1.selected_iff _).mp ((d.selectedE_iff a).mpr ha)
  exact ⟨(d.square a).trans h,h⟩

theorem selected_disjoint (a : At d.F d.C) (b : At d.F d.E)
    (ha : a ∈ d.selectedC0) (hb : b ∈ d.selectedE0) : a.index ≠ b.index := by
  have h₁ := d.selectedC0_outside a ha
  have h₂ := d.selectedE0_inside b hb
  omega

theorem selectedC0_gap_exclusion (a : At d.F d.C) (ha : a ∈ d.selectedC0) :
    a.index < (repeated d.C d.pre).length ∨
      (repeated d.C d.pre).length+d.U.length+(repeated d.E d.es).length+d.V.length ≤ a.index := by
  have hm : a.index ∈ copyOffsets d.outer0 := by
    rw [← d.bc0.selected_indices]; exact List.mem_map.mpr ⟨a,ha,rfl⟩
  have h := GapLogical.selected_outside d.C d.pre d.post [] (d.U++(repeated d.E d.es++d.V)) [] a.index
    (by simpa only [outer0,List.nil_append,List.append_nil] using hm)
  simpa only [List.append_nil,List.length_append,Nat.add_assoc] using h

theorem selectedC_order (a b : At d.F d.C) (ha : a ∈ d.selectedC0)
    (hb : b ∈ d.selectedC0) (h : a.index < b.index) : (d.e0.get a).index < (d.e0.get b).index := by
  rw [d.e0_index,d.e0_index]
  exact splice_outside_strict _ _ _ _ _ _ (d.selectedC0_outside a ha) (d.selectedC0_outside b hb) h

theorem selectedE_order (a b : At d.F d.E) (ha : a ∈ d.selectedE0)
    (hb : b ∈ d.selectedE0) (h : a.index < b.index) : (d.c0.get a).index < (d.c0.get b).index := by
  have h₁ := d.selectedE0_inside a ha
  have h₂ := d.selectedE0_inside b hb
  rw [d.c0_inside a h₁.1 h₁.2,d.c0_inside b h₂.1 h₂.2]
  omega

end Disjoint.Data
end DosenPetric.Reduced.Gentzen
