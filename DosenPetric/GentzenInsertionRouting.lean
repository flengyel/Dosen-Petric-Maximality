module

public import DosenPetric.GentzenInsertionPositions

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.GapInsertion.Data
universe u
variable {P : Type u} (d : Data P)

theorem product_square : comp (ofTerm d.c1.product) (ofTerm d.tUpper.product) =
    comp (ofTerm d.tLower.product) (ofTerm d.c0.product) := by
  apply product_positions
  intro A a
  rw [Laws.assoc,Route.product_get,Route.product_get,Laws.assoc,Route.product_get,Route.product_get]
  exact congrArg (fun x => ofTerm x.projection) (d.square a)

theorem coproduct_square : comp (ofTerm d.tUpper.coproduct) (ofTerm d.c1.coproduct) =
    comp (ofTerm d.c0.coproduct) (ofTerm d.tLower.coproduct) := by
  apply coproduct_positions
  intro A a
  rw [← Laws.assoc,Route.coproduct_get,Route.coproduct_get,
    ← Laws.assoc,Route.coproduct_get,Route.coproduct_get]
  exact congrArg (fun x => ofTerm x.injection) (d.square a)

theorem selected0_mem (a : At d.U0 d.C) :
    a ∈ d.selected0 ↔ a.index ∈ copyOffsets d.gs0 := by
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

theorem selected1_mem (a : At d.U1 d.C) :
    a ∈ d.selected1 ↔ a.index ∈ copyOffsets d.gs1 := by
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

/-- No selected copy is the new thinning position, even when E=C. -/
theorem selected1_parametric (a : At d.U1 d.C) (ha : a ∈ d.selected1) :
    a.index ≠ d.upBefore.length := by
  have h := (d.selected1_iff a).mp ha
  have hi := congrArg At.index h
  rw [c1_index,keep1_index] at hi
  intro he
  rw [he,d.insertedIndex] at hi
  cases d.lowerOrder <;> omega

theorem selected_embedded_iff (a : At d.U0 d.C) :
    d.tUpper.get a ∈ d.selected1 ↔ a ∈ d.selected0 := by
  rw [selected1_iff,selected0_iff,d.square,← d.retained]
  exact ⟨thin_get_injective _ _ _ _ _,fun h => congrArg d.tLower.get h⟩

/-- Equality of complete ordered lists, rather than just membership inclusion. -/
theorem selected_transport : d.selected1 = d.selected0.map d.tUpper.get := by
  have h0 : At.Ordered d.selected0 := by
    apply (selectedCopies_ordered d.C d.gs0 d.tail0).map
    intro a b h
    simpa only [At.index_cast] using h
  have h1 : At.Ordered d.selected1 := by
    apply (selectedCopies_ordered d.C d.gs1 d.tail1).map
    intro a b h
    simpa only [At.index_cast] using h
  apply At.ordered_ext _ _ h1
  · apply h0.map
    intro a b hab
    simp only [tUpper_index]
    exact liftIndex_strict _ _ _ hab
  · intro y
    constructor
    · intro hy
      obtain ⟨a,ha⟩ := thin_old_position d.upBefore d.upAfter d.E y (d.selected1_parametric y hy)
      change d.tUpper.get a = y at ha
      refine List.mem_map.mpr ⟨a,?_,ha⟩
      apply (d.selected_embedded_iff a).mp
      rwa [ha]
    · rintro hy
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hy
      exact (d.selected_embedded_iff a).mpr ha

theorem selected0_length : d.selected0.length = d.gs0.length := by
  simp only [selected0,List.length_map,selectedCopies_length]

theorem selected1_length : d.selected1.length = d.gs1.length := by
  simp only [selected1,List.length_map,selectedCopies_length]

/-- The inserted fixed position has exactly the inserted upper predecessor. -/
theorem canonical_inserted_fiber :
    (TraceRoute.full (copies d.C d.gs1 d.tail1)).fiber (d.zLower.cast d.lower1.symm) =
      [d.zUpper.cast d.upper1.symm] := by
  have hm : d.zUpper.cast d.upper1.symm ∈
      (TraceRoute.full (copies d.C d.gs1 d.tail1)).fiber (d.zLower.cast d.lower1.symm) :=
    (TraceRoute.fiber_correct ..).mpr ((TraceRoute.get_full ..).trans (congrArg some d.canonical_inserted))
  rw [fiber_copies_fixed d.C d.gs1 d.tail1 _ d.canonical_inserted_fixed] at hm ⊢
  rw [List.mem_singleton.mp hm]

end DosenPetric.Reduced.Gentzen.GapInsertion.Data
