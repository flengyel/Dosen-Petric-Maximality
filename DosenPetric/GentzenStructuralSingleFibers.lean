module

public import DosenPetric.GentzenStructuralResiduals

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace Route
variable {F U : List (NormalForm P)} {C : NormalForm P}

/-- Typed uniqueness gives uniqueness of ordinal coordinates, even across labels. -/
theorem singleFiber_of_unique (r : Route F U) (x : At F C) (y : At U C)
    (hy : r.get y = x) (hu : ∀ b : At U C, r.get b = x → b = y) : r.SingleFiber x y := by
  refine ⟨hy,?_⟩
  intro E b hb
  have he := (r.get b).formula_eq x hb
  cases he
  have hb' : r.get b = x := by apply At.index_injective; exact hb
  exact congrArg At.index (hu b hb')

theorem singleFiber_of_injective (r : Route F U)
    (hi : ∀ {E : NormalForm P} (a b : At U E), r.get a = r.get b → a = b)
    (y : At U C) : r.SingleFiber (r.get y) y :=
  singleFiber_of_unique r _ y rfl (fun b hb => hi b y hb)

end Route
namespace StructuralProgram

/-- Every exchange position has one selected predecessor, including empty swapped blocks. -/
theorem exchange_singleFiber (F X Y U : List (NormalForm P))
    {C : NormalForm P} (y : At (F ++ X ++ Y ++ U) C) :
    (.exchange F X Y U : StructuralProgram P _ _).route.SingleFiber
      (y.swapBlocks F X Y U) y := by
  apply Route.singleFiber_of_unique
  · rw [route_get]; rfl
  · intro b hb
    rw [route_get] at hb
    exact At.swapBlocks_injective F X Y U b y hb

/-- Every old thinning position has one predecessor, distinct from the inserted slot. -/
theorem thin_singleFiber (F U : List (NormalForm P)) (E : NormalForm P)
    {C : NormalForm P} (y : At (F ++ U) C) :
    (.thin F U E : StructuralProgram P _ _).route.SingleFiber
      ((Route.thin F U E).get y) y := by
  apply Route.singleFiber_of_unique
  · rw [route_get]; rfl
  · intro b hb
    rw [route_get] at hb
    exact thin_get_injective F U E b y hb

/-- All positions outside the actual contracted tag have a unique fixed upper copy. -/
theorem contract_singleFiber (E : NormalForm P) (gs : List (List (NormalForm P)))
    (U : List (NormalForm P)) (hn : 2 ≤ gs.length) {C : NormalForm P}
    (x : At (gaps gs ++ E :: U) C) (hx : x.index ≠ (gaps gs).length) :
    (.contract E gs U hn : StructuralProgram P _ _).route.SingleFiber x
      (fixedCopyAt E gs U x hx) := by
  apply Route.singleFiber_of_unique
  · rw [route_get]
    apply At.index_injective
    rw [get, copies_index, fixedCopyAt_index]
    exact copyIndex_fixed gs x.index hx
  · intro b hb
    apply At.index_injective
    rw [fixedCopyAt_index]
    apply copyIndex_fixed_unique gs b.index x.index hx
    have he := congrArg At.index hb
    simpa only [route_get, get, copies_index] using he

end StructuralProgram
end DosenPetric.Reduced.Gentzen
