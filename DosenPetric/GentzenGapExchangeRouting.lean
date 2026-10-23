module

public import DosenPetric.GentzenExchangeEmbeddings

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.GapExchange.Data
universe u
variable {P : Type u} (d : Data P)

def eUpperL := ofTerm (exchange .conj d.upBefore d.X d.Y d.upAfter).invTerm
def eLowerL := ofTerm (exchange .conj d.loBefore d.X d.Y d.loAfter).invTerm
def eUpperR := ofTerm (exchange .disj d.upBefore d.X d.Y d.upAfter).toTerm
def eLowerR := ofTerm (exchange .disj d.loBefore d.X d.Y d.loAfter).toTerm

theorem product_square : comp (ofTerm d.c1.product) d.eUpperL =
    comp d.eLowerL (ofTerm d.c0.product) := by
  apply product_positions
  intro A a
  change comp (comp _ (ofTerm (exchange .conj d.upBefore d.X d.Y d.upAfter).invTerm)) (ofTerm a.projection) =
    comp (comp (ofTerm (exchange .conj d.loBefore d.X d.Y d.loAfter).invTerm) _) (ofTerm a.projection)
  rw [Laws.assoc,exchangeL_projection,Route.product_get,Laws.assoc,Route.product_get,exchangeL_projection]
  exact congrArg (fun x => ofTerm x.projection) (d.square a)

theorem coproduct_square : comp d.eUpperR (ofTerm d.c1.coproduct) =
    comp (ofTerm d.c0.coproduct) d.eLowerR := by
  apply coproduct_positions
  intro A a
  change comp (ofTerm a.injection) (comp (ofTerm (exchange .disj d.upBefore d.X d.Y d.upAfter).toTerm) _) =
    comp (ofTerm a.injection) (comp _ (ofTerm (exchange .disj d.loBefore d.X d.Y d.loAfter).toTerm))
  rw [← Laws.assoc,exchangeR_injection,Route.coproduct_get,← Laws.assoc,Route.coproduct_get,exchangeR_injection]
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


theorem selected0_outside (a : At d.U0 d.C) (ha : a ∈ d.selected0) :
    a.index < d.upBefore.length ∨ d.upBefore.length+d.X.length+d.Y.length ≤ a.index :=
  d.outside0 a.index ((d.selected0_mem a).mp ha)

/-- Index preservation holds on selected copies only, not on arbitrary positions. -/
theorem selected0_index_fixed (a : At d.U0 d.C) (ha : a ∈ d.selected0) :
    (d.swapUpper a).index = a.index := by
  rw [swapUpper_index]
  exact exchange_outside d.upBefore.length d.X.length d.Y.length a.index (d.selected0_outside a ha)

theorem selected_embedded_iff (a : At d.U0 d.C) :
    d.swapUpper a ∈ d.selected1 ↔ a ∈ d.selected0 := by
  rw [selected1_iff,selected0_iff,d.square,← d.retained]
  exact ⟨fun h => At.swapBlocks_injective d.loBefore d.X d.Y d.loAfter _ _ h,fun h => congrArg d.swapLower h⟩

/-- No global order preservation of block swap is asserted or used. -/
theorem selected_transport : d.selected1 = d.selected0.map d.swapUpper := by
  have h0 : At.Ordered d.selected0 := by
    apply (selectedCopies_ordered d.C d.gs0 d.tail0).map
    intro a b h
    simpa only [At.index_cast] using h
  have h1 : At.Ordered d.selected1 := by
    apply (selectedCopies_ordered d.C d.gs1 d.tail1).map
    intro a b h
    simpa only [At.index_cast] using h
  have hm : At.Ordered (d.selected0.map d.swapUpper) := by
    apply List.pairwise_map.mpr
    apply h0.imp_of_mem
    intro a b ha hb hab
    rw [d.selected0_index_fixed a ha,d.selected0_index_fixed b hb]
    exact hab
  apply At.ordered_ext _ _ h1 hm
  intro y
  constructor
  · intro hy
    let a := y.swapBlocks d.upBefore d.Y d.X d.upAfter
    have he : d.swapUpper a = y := At.swapBlocks_inverse ..
    exact List.mem_map.mpr ⟨a,(d.selected_embedded_iff a).mp (he.symm ▸ hy),he⟩
  · intro hy
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hy
    exact (d.selected_embedded_iff a).mpr ha

theorem selected1_outside (a : At d.U1 d.C) (ha : a ∈ d.selected1) :
    a.index < d.upBefore.length ∨ d.upBefore.length+d.Y.length+d.X.length ≤ a.index := by
  rw [d.selected_transport] at ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  rw [d.selected0_index_fixed b hb]
  have h := d.selected0_outside b hb
  omega

theorem selected0_length : d.selected0.length = d.gs0.length := by
  simp only [selected0,List.length_map,selectedCopies_length]

theorem selected1_length : d.selected1.length = d.gs1.length := by
  simp only [selected1,List.length_map,selectedCopies_length]

end DosenPetric.Reduced.Gentzen.GapExchange.Data
