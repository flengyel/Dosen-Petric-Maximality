module

public import DosenPetric.GentzenSelectedThinningData
public import DosenPetric.GentzenRouteFiberSums

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.SelectedThinning.Data
universe u
variable {P : Type u} (d : Data P)

theorem old_position {A : NormalForm P} (b : At d.U A) (hb : b.index ≠ d.z.index) :
    ∃ a : At d.F A, d.t.get a = b := by
  cases At.cases_append d.F [d.C] b with
  | inl h =>
    obtain ⟨a,ha⟩ := h
    refine ⟨a,At.index_injective _ _ ?_⟩
    rw [d.t_index,ha,At.index_before]
  | inr h =>
    obtain ⟨c,rfl⟩ := h
    cases c with
    | here => exact False.elim (hb rfl)
    | there c => cases c

theorem selected_embedded (a : At d.F d.C) :
    d.t.get a ∈ d.outer.selected ↔ a ∈ d.inner.selected := by
  rw [d.outer.selected_iff,d.inner.selected_iff,d.square]
  exact ⟨fun h => d.e_injective _ _ (h.trans d.retained.symm),
    fun h => (congrArg d.e.get h).trans d.retained⟩

/-- The new thinning leaf is appended to the complete ordered old-copy list. -/
theorem selected_transport : d.outer.selected = d.inner.selected.map d.t.get ++ [d.z] := by
  have hm : At.Ordered (d.inner.selected.map d.t.get) := by
    apply d.inner.selected_ordered.map
    intro a b h
    simpa only [d.t_index] using h
  have ht : At.Ordered (d.inner.selected.map d.t.get ++ [d.z]) := by
    apply List.pairwise_append.mpr
    refine ⟨hm,.cons (by intro a h; cases h) .nil,?_⟩
    intro a ha b hb
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp ha
    have he : b = d.z := List.mem_singleton.mp hb
    rw [he,d.t_index,d.z_index]
    exact a.index_lt
  apply At.ordered_ext _ _ d.outer.selected_ordered ht
  intro b
  rw [List.mem_append,List.mem_singleton]
  constructor
  · intro hb
    by_cases he : b.index = d.z.index
    · exact .inr (At.index_injective _ _ he)
    · obtain ⟨a,ha⟩ := d.old_position b he
      exact .inl (List.mem_map.mpr ⟨a,(d.selected_embedded a).mp (ha.symm ▸ hb),ha⟩)
  · rintro (hb | rfl)
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      exact (d.selected_embedded a).mpr ha
    · exact d.inserted_selected

theorem selected_length : d.outer.selected.length = d.gs.length+1 := by
  exact d.outer.selected_length.trans d.outer_count
theorem old_selected_length : d.inner.selected.length = d.gs.length := d.inner.selected_length

theorem t_fiber {A : NormalForm P} (a : At d.F A) :
    (TraceRoute.full d.t).fiber (d.t.get a) = [a] := by
  apply TraceRoute.fiber_single
  intro b
  rw [TraceRoute.get_full,Option.some.injEq]
  exact ⟨d.t_injective b a,fun h => by cases h; rfl⟩
theorem e_fiber {A : NormalForm P} (z : At d.K A) :
    (TraceRoute.full d.e).fiber z = [d.back z] := by
  apply TraceRoute.fiber_single
  intro a
  rw [TraceRoute.get_full,Option.some.injEq]
  exact ⟨fun h => d.e_injective a (d.back z) (h.trans (d.e_back z).symm),
    fun h => h ▸ d.e_back z⟩

theorem outer_retained_fiber : (TraceRoute.full d.outer.route).fiber d.x =
    d.inner.selected.map d.t.get ++ [d.z] :=
  d.outer.selected_fiber.trans d.selected_transport

theorem old_composite_fiber : (TraceRoute.full (d.t.map d.outer.route.get)).fiber d.x = d.inner.selected := by
  apply At.ordered_ext _ _ (TraceRoute.fiber_ordered _ _) d.inner.selected_ordered
  intro a
  rw [TraceRoute.fiber_correct,TraceRoute.get_full,Option.some.injEq,Route.get_map,
    ← d.outer.selected_iff,d.selected_embedded]
theorem new_composite_fiber : (TraceRoute.full (d.inner.route.map d.e.get)).fiber d.x = d.inner.selected := by
  apply At.ordered_ext _ _ (TraceRoute.fiber_ordered _ _) d.inner.selected_ordered
  intro a
  rw [TraceRoute.fiber_correct,TraceRoute.get_full,Option.some.injEq,Route.get_map,← d.square,
    ← d.outer.selected_iff,d.selected_embedded]

theorem back_fixed {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.x.index) :
    (d.back z).index ≠ d.inner.keep.index := by
  have h₀ := congrArg At.index (d.e_back z)
  have h₁ := congrArg At.index d.retained
  rw [d.e_index] at h₀ h₁
  intro he
  rw [he,h₁] at h₀
  exact hz h₀.symm

def original {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.x.index) : At d.F A :=
  d.inner.fixed (d.back z) (d.back_fixed z hz)
theorem original_new {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.x.index) :
    d.e.get (d.inner.route.get (d.original z hz)) = z := by
  rw [original,d.inner.fixed_get,d.e_back]
theorem original_old {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.x.index) :
    d.outer.route.get (d.t.get (d.original z hz)) = z := by rw [d.square,d.original_new]

theorem original_unique {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.x.index)
    (a : At d.F A) (ha : d.e.get (d.inner.route.get a) = z) : a = d.original z hz := by
  apply d.inner.fixed_unique (d.back z) (d.back_fixed z hz) a
  exact d.e_injective _ _ (ha.trans (d.e_back z).symm)

theorem outer_fixed_fiber {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.x.index) :
    (TraceRoute.full d.outer.route).fiber z = [d.t.get (d.original z hz)] := by
  have he := d.outer.fixed_fiber z hz
  have hx := d.outer.fixed_unique z hz (d.t.get (d.original z hz)) (d.original_old z hz)
  rw [← hx] at he
  exact he

theorem other_fibers {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.x.index) :
    (TraceRoute.full (d.t.map d.outer.route.get)).fiber z = [d.original z hz] ∧
    (TraceRoute.full (d.inner.route.map d.e.get)).fiber z = [d.original z hz] := by
  constructor <;> apply TraceRoute.fiber_single <;> intro a <;>
    rw [TraceRoute.get_full,Option.some.injEq,Route.get_map]
  · exact ⟨fun h => d.original_unique z hz a ((d.square a).symm.trans h),
      fun h => h ▸ d.original_old z hz⟩
  · exact ⟨d.original_unique z hz a,fun h => h ▸ d.original_new z hz⟩

theorem product_square :
    comp (ofTerm d.outer.route.product) (ofTerm d.t.product) =
      comp (ofTerm d.e.product) (ofTerm d.inner.route.product) := by
  apply product_positions
  intro A a
  rw [Laws.assoc,Route.product_get,Route.product_get,Laws.assoc,Route.product_get,Route.product_get]
  exact congrArg (fun x => ofTerm x.projection) (d.square a)
theorem coproduct_square :
    comp (ofTerm d.t.coproduct) (ofTerm d.outer.route.coproduct) =
      comp (ofTerm d.inner.route.coproduct) (ofTerm d.e.coproduct) := by
  apply coproduct_positions
  intro A a
  rw [← Laws.assoc,Route.coproduct_get,Route.coproduct_get,
    ← Laws.assoc,Route.coproduct_get,Route.coproduct_get]
  exact congrArg (fun x => ofTerm x.injection) (d.square a)

end DosenPetric.Reduced.Gentzen.SelectedThinning.Data
