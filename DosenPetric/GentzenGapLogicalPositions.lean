module

public import DosenPetric.GentzenGapLogicalData

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace At

theorem fixed_ordered (Γ X Y Θ : List (NormalForm P)) {E : NormalForm P}
    (xs : List (At (Γ ++ (X ++ Θ)) E)) (hx : Ordered xs) :
    Ordered (xs.flatMap (fun a => (fixed Γ X Y Θ a).toList)) := by
  induction xs with
  | nil => exact .nil
  | cons a xs ih =>
    simp only [List.flatMap_cons]
    cases he : fixed Γ X Y Θ a with
    | none => simpa only [he,Option.toList_none,List.nil_append] using ih hx.of_cons
    | some a' =>
      simp only [Option.toList_some,List.singleton_append]
      apply List.Pairwise.cons
      · intro b' hb'
        obtain ⟨b,hb,hb'⟩ := List.mem_flatMap.mp hb'
        exact fixed_strict Γ X Y Θ a b a' b' he (Option.mem_toList.mp hb') (List.rel_of_pairwise_cons hx hb)
      · exact ih hx.of_cons

end At

namespace GapLogical.Data
variable {o : Op} (d : Data P o)

theorem selected0_mem (a : At d.U0 d.C) : a ∈ d.selected0 ↔ a.index ∈ copyOffsets d.gs0 := by
  simp only [selected0,List.mem_map]
  constructor
  · rintro ⟨b,hb,he⟩
    have hi := congrArg At.index he
    rw [At.index_cast] at hi
    rw [← hi]
    exact (selectedCopies_mem ..).mp hb
  · intro ha
    refine ⟨a.cast d.upper0.symm,?_,?_⟩
    · apply (selectedCopies_mem ..).mpr
      simpa only [At.index_cast] using ha
    · apply At.index_injective
      simp only [At.index_cast]

theorem selected1_mem (a : At d.U1 d.C) : a ∈ d.selected1 ↔ a.index ∈ copyOffsets d.gs1 := by
  simp only [selected1,List.mem_map]
  constructor
  · rintro ⟨b,hb,he⟩
    have hi := congrArg At.index he
    rw [At.index_cast] at hi
    rw [← hi]
    exact (selectedCopies_mem ..).mp hb
  · intro ha
    refine ⟨a.cast d.upper1.symm,?_,?_⟩
    · apply (selectedCopies_mem ..).mpr
      simpa only [At.index_cast] using ha
    · apply At.index_injective
      simp only [At.index_cast]

theorem selected0_outside (a : At d.U0 d.C) (ha : a ∈ d.selected0) :
    a.index < d.upBefore.length ∨ d.upBefore.length+2 ≤ a.index := d.outside0 a.index ((d.selected0_mem a).mp ha)
theorem selected1_outside (a : At d.U1 d.C) (ha : a ∈ d.selected1) :
    a.index < d.upBefore.length ∨ d.upBefore.length+1 ≤ a.index := d.outside1 a.index ((d.selected1_mem a).mp ha)

theorem selected0_survives (a : At d.U0 d.C) (ha : a ∈ d.selected0) : ∃ b, d.uParent a = some b :=
  At.fixed_survives d.upBefore [d.A,d.B] [d.D] d.upAfter a (d.selected0_outside a ha)

def selectedImage (a : At d.U0 d.C) (ha : a ∈ d.selected0) : At d.U1 d.C :=
  At.fixedImage d.upBefore [d.A,d.B] [d.D] d.upAfter a (d.selected0_outside a ha)
theorem selectedImage_spec (a : At d.U0 d.C) (ha : a ∈ d.selected0) :
    d.uParent a = some (d.selectedImage a ha) := At.fixedImage_spec ..

theorem retained : d.kParent d.keep0 = some d.keep1 := by
  apply At.option_index_injective
  have hi := At.fixed_index d.loBefore [d.A,d.B] [d.D] d.loAfter d.keep0
  change (d.kParent d.keep0).map At.index = parentIndex d.loBefore.length 2 1 d.keep0.index at hi
  rw [d.keep0_index,d.retainedIndex] at hi
  exact hi.trans (congrArg some d.keep1_index.symm)

theorem selected0_iff (a : At d.U0 d.C) : a ∈ d.selected0 ↔ d.c0.get a = d.keep0 := by
  rw [selected0_mem,← copyIndex_selected]
  constructor
  · intro h
    apply At.index_injective
    rw [c0_index,keep0_index]
    exact h
  · intro h
    have hi := congrArg At.index h
    simpa only [c0_index,keep0_index] using hi

theorem selected1_iff (a : At d.U1 d.C) : a ∈ d.selected1 ↔ d.c1.get a = d.keep1 := by
  rw [selected1_mem,← copyIndex_selected]
  constructor
  · intro h
    apply At.index_injective
    rw [c1_index,keep1_index]
    exact h
  · intro h
    have hi := congrArg At.index h
    simpa only [c1_index,keep1_index] using hi

theorem selected_parent_iff (a : At d.U0 d.C) (b : At d.U1 d.C) (h : d.uParent a = some b) :
    b ∈ d.selected1 ↔ a ∈ d.selected0 := by
  have hs := d.square a
  rw [h,Option.map_some] at hs
  rw [selected0_iff,selected1_iff]
  constructor
  · intro hb
    apply At.fixed_injective d.loBefore [d.A,d.B] [d.D] d.loAfter _ _ d.keep1
      (hs.symm.trans (congrArg some hb)) d.retained
  · intro ha
    rw [ha,d.retained] at hs
    exact Option.some.inj hs

/-- Complete ordered transport; every selected source entry is separately proved to survive. -/
theorem selected_transport : d.selected0.flatMap (fun a => (d.uParent a).toList) = d.selected1 := by
  have h0 : At.Ordered d.selected0 := by
    apply (selectedCopies_ordered d.C d.gs0 d.tail0).map
    intro a b h
    simpa only [At.index_cast] using h
  have h1 : At.Ordered d.selected1 := by
    apply (selectedCopies_ordered d.C d.gs1 d.tail1).map
    intro a b h
    simpa only [At.index_cast] using h
  apply At.ordered_ext _ _ (At.fixed_ordered d.upBefore [d.A,d.B] [d.D] d.upAfter d.selected0 h0) h1
  intro b
  constructor
  · intro hb
    obtain ⟨a,ha,hb⟩ := List.mem_flatMap.mp hb
    exact (d.selected_parent_iff a b (Option.mem_toList.mp hb)).mpr ha
  · intro hb
    obtain ⟨a,ha⟩ := At.fixed_survives d.upBefore [d.D] [d.A,d.B] d.upAfter b (d.selected1_outside b hb)
    have hp := (At.fixed_reverse d.upBefore [d.A,d.B] [d.D] d.upAfter a b).mpr ha
    exact List.mem_flatMap.mpr ⟨a,(d.selected_parent_iff a b hp).mp hb,Option.mem_toList.mpr hp⟩

theorem selected0_length : d.selected0.length = d.gs0.length := by
  simp only [selected0,List.length_map,selectedCopies_length]
theorem selected1_length : d.selected1.length = d.gs0.length := by
  simp only [selected1,List.length_map,selectedCopies_length,d.count_eq]

theorem consumed_first : d.uParent d.aUpper = none :=
  At.fixed_middle d.upBefore [d.A,d.B] [d.D] d.upAfter (.here d.A [d.B])

theorem consumed_second : d.uParent d.bUpper = none :=
  At.fixed_middle d.upBefore [d.A,d.B] [d.D] d.upAfter (.there (.here d.B []))

theorem principal_distinct : d.zLower.index ≠ d.keep1.index := by
  simp only [zLower,At.index_shift,At.index,Nat.add_zero,keep1_index]
  exact d.principalDistinct

/-- Partial inverse on every final nonprincipal whole-formula position. -/
def lowerBack {E : NormalForm P} (z : At d.K1 E) (hz : z.index ≠ d.loBefore.length) : At d.K0 E :=
  At.fixedImage d.loBefore [d.D] [d.A,d.B] d.loAfter z (by simp only [List.length_cons,List.length_nil]; omega)

theorem lowerBack_spec {E : NormalForm P} (z : At d.K1 E) (hz : z.index ≠ d.loBefore.length) :
    d.kParent (d.lowerBack z hz) = some z :=
  (At.fixed_reverse d.loBefore [d.A,d.B] [d.D] d.loAfter _ z).mpr (At.fixedImage_spec ..)

end GapLogical.Data
end DosenPetric.Reduced.Gentzen
