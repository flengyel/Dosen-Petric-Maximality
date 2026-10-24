module

public import DosenPetric.GentzenSelectedLogicalData

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.SelectedLogical.Data
universe u
variable {P : Type u} {o : Op} (d : Data P o)

def oldTrace : TraceRoute d.K d.F :=
  TraceRoute.ofMap _ _ (fun a => (d.uParent a).map d.outer.route.get)
def newTrace : TraceRoute d.K d.F :=
  TraceRoute.ofMap _ _ (fun a => (d.iParent (d.inner.route.get a)).map d.last.route.get)
theorem trace_square {E : NormalForm P} (a : At d.F E) :
    d.oldTrace.get a = d.newTrace.get a := by
  rw [oldTrace,newTrace,TraceRoute.get_ofMap,TraceRoute.get_ofMap]
  exact d.partial_square a
theorem old_prefix {E : NormalForm P} (a : At d.s.F E) :
    d.oldTrace.get (a.before [d.A,d.B]) = some (d.outer.route.get (a.before [d.C])) := by
  rw [oldTrace,TraceRoute.get_ofMap,d.u_prefix,Option.map_some]

theorem parent_original {E : NormalForm P} (a : At d.F E) (v : At d.U E)
    (hp : d.uParent a = some v) :
    ∃ b : At d.s.F E, a = b.before [d.A,d.B] ∧ v = b.before [d.C] := by
  cases At.cases_append d.s.F [d.A,d.B] a with
  | inl h =>
    obtain ⟨a,rfl⟩ := h
    exact ⟨a,rfl,(Option.some.inj ((d.u_prefix a).symm.trans hp)).symm⟩
  | inr h =>
    obtain ⟨a,rfl⟩ := h
    cases a with
    | here => rw [show At.shift d.s.F (.here d.A [d.B]) = d.a from rfl,d.consumed_a] at hp; cases hp
    | there a =>
      cases a with
      | here => rw [show At.shift d.s.F (.there (.here d.B [])) = d.b from rfl,d.consumed_b] at hp; cases hp
      | there a => cases a

theorem selected_prefix (a : At d.s.F d.C) :
    a.before [d.A,d.B] ∈ d.inner.selected ↔ a ∈ d.s.inner.selected := by
  rw [d.inner_selected,List.mem_map]
  constructor
  · rintro ⟨b,hb,he⟩
    have hi := congrArg At.index he
    rw [At.index_before,At.index_before] at hi
    exact At.index_injective b a hi ▸ hb
  · intro ha; exact ⟨a,ha,rfl⟩

theorem selected_transport :
    d.inner.selected.flatMap (fun a => (d.uParent a).toList)++[d.s.z] = d.outer.selected := by
  have he (xs : List (At d.s.F d.C)) :
      (xs.map (fun a => a.before [d.A,d.B])).flatMap (fun a => (d.uParent a).toList) =
        xs.map (fun a => a.before [d.C]) := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      simp only [List.map_cons,List.flatMap_cons,d.u_prefix,Option.toList_some,
        List.singleton_append,ih]
  rw [d.inner_selected,he]
  exact d.outer_selected.symm

theorem selected_survives (a : At d.F d.C) (ha : a ∈ d.inner.selected) :
    ∃ b, d.uParent a = some b := by
  rw [d.inner_selected,List.mem_map] at ha
  obtain ⟨b,_,rfl⟩ := ha
  exact ⟨_,d.u_prefix b⟩
theorem inner_selected_length : d.inner.selected.length = d.gs.length := d.inner.selected_length
theorem outer_selected_length : d.outer.selected.length = d.gs.length+1 :=
  d.outer.selected_length.trans d.s.outer_count
theorem last_selected_length : d.last.selected.length = 2 := d.last.selected_length

theorem old_retained_fiber : d.oldTrace.fiber d.x = d.inner.selected := by
  apply At.ordered_ext _ _ (TraceRoute.fiber_ordered _ _) d.inner.selected_ordered
  intro a
  rw [TraceRoute.fiber_correct]
  constructor
  · intro ha
    rw [oldTrace,TraceRoute.get_ofMap] at ha
    cases hp : d.uParent a with
    | none => rw [hp] at ha; cases ha
    | some v =>
      obtain ⟨a₀,rfl,rfl⟩ := d.parent_original a v hp
      rw [d.u_prefix,Option.map_some,Option.some.injEq] at ha
      apply (d.selected_prefix a₀).mpr
      apply (d.s.selected_embedded a₀).mp
      apply (d.outer.selected_iff _).mpr
      exact (congrArg d.outer.route.get (d.t_before a₀)).trans ha
  · intro ha
    rw [d.inner_selected,List.mem_map] at ha
    obtain ⟨a,ha,rfl⟩ := ha
    rw [d.old_prefix,Option.some.injEq,← d.t_before]
    exact (d.outer.selected_iff _).mp ((d.s.selected_embedded a).mpr ha)

theorem new_retained_fiber : d.newTrace.fiber d.x = d.inner.selected :=
  (TraceRoute.fiber_ext _ _ _ _ (fun a => by rw [d.trace_square])).symm.trans d.old_retained_fiber
theorem outer_retained_fiber : (TraceRoute.full d.outer.route).fiber d.x =
    d.s.inner.selected.map (fun a => a.before [d.C])++[d.s.z] :=
  d.outer.selected_fiber.trans d.outer_selected
theorem last_retained_fiber : (TraceRoute.full d.last.route).fiber d.x = [d.k,d.q] := by
  rw [← d.last_keep]
  exact d.last.selected_fiber.trans d.last_selected
theorem logical_principal_fiber : (TraceRoute.ofMap _ _ d.uParent).fiber d.s.z = [] := by
  apply TraceRoute.fiber_empty
  intro a ha
  rw [TraceRoute.get_ofMap] at ha
  obtain ⟨b,_,hb⟩ := d.parent_original a d.s.z ha
  have he := congrArg At.index hb
  rw [d.s.z_index,At.index_before] at he
  have hi := b.index_lt
  omega
theorem middle_parent_original {E : NormalForm P} (a : At d.I E) (v : At d.J E)
    (hp : d.iParent a = some v) :
    ∃ b : At d.s.I E, a = b.before [d.A,d.B] ∧ v = b.before [d.C] := by
  cases At.cases_append d.s.I [d.A,d.B] a with
  | inl h =>
    obtain ⟨a,rfl⟩ := h
    exact ⟨a,rfl,(Option.some.inj ((d.i_prefix a).symm.trans hp)).symm⟩
  | inr h =>
    obtain ⟨a,rfl⟩ := h
    cases a with
    | here => rw [show At.shift d.s.I (.here d.A [d.B]) = d.aI from rfl,d.inner_consumed_a] at hp; cases hp
    | there a =>
      cases a with
      | here => rw [show At.shift d.s.I (.there (.here d.B [])) = d.bI from rfl,d.inner_consumed_b] at hp; cases hp
      | there a => cases a
theorem middle_principal_fiber : (TraceRoute.ofMap _ _ d.iParent).fiber d.q = [] := by
  apply TraceRoute.fiber_empty
  intro a ha
  rw [TraceRoute.get_ofMap] at ha
  obtain ⟨b,_,hb⟩ := d.middle_parent_original a d.q ha
  have hi := congrArg At.index hb
  simp only [q,At.index_shift,At.index,Nat.add_zero,At.index_before] at hi
  have hl := b.index_lt
  omega

def original {E : NormalForm P} (z : At d.K E) (hz : z.index ≠ d.x.index) : At d.F E :=
  (d.s.original z hz).before [d.A,d.B]
def oldFixed {E : NormalForm P} (z : At d.K E) (hz : z.index ≠ d.x.index) : At d.U E :=
  (d.s.original z hz).before [d.C]
def innerFixed {E : NormalForm P} (z : At d.K E) : At d.I E :=
  (d.s.back z).before [d.A,d.B]
def newFixed {E : NormalForm P} (z : At d.K E) : At d.J E :=
  (d.s.back z).before [d.C]
theorem original_old {E : NormalForm P} (z : At d.K E) (hz : z.index ≠ d.x.index) :
    d.outer.route.get (d.oldFixed z hz) = z := by
  rw [oldFixed,← d.t_before]
  exact d.s.original_old z hz
theorem original_inner {E : NormalForm P} (z : At d.K E) (hz : z.index ≠ d.x.index) :
    d.inner.route.get (d.original z hz) = d.innerFixed z := by
  rw [original,ContractionBlock.extend_before,innerFixed]
  exact congrArg (fun a : At d.s.I E => a.before [d.A,d.B]) (d.s.inner.fixed_get (d.s.back z) (d.s.back_fixed z hz))
theorem original_last {E : NormalForm P} (z : At d.K E) :
    d.last.route.get (d.newFixed z) = z := by
  rw [newFixed,d.last_prefix,d.s.e_back]
theorem original_parent {E : NormalForm P} (z : At d.K E) (hz : z.index ≠ d.x.index) :
    d.uParent (d.original z hz) = some (d.oldFixed z hz) := d.u_prefix _
theorem fixed_parent {E : NormalForm P} (z : At d.K E) :
    d.iParent (d.innerFixed z) = some (d.newFixed z) := d.i_prefix _
theorem inner_fixed {E : NormalForm P} (z : At d.K E) (hz : z.index ≠ d.x.index) :
    (d.innerFixed z).index ≠ d.inner.keep.index := by
  rw [innerFixed,ContractionBlock.extend_keep,At.index_before,At.index_before]
  exact d.s.back_fixed z hz

theorem outer_fixed_fiber {E : NormalForm P} (z : At d.K E) (hz : z.index ≠ d.x.index) :
    (TraceRoute.full d.outer.route).fiber z = [d.oldFixed z hz] := by
  have h := d.outer.fixed_fiber z hz
  have he := d.outer.fixed_unique z hz _ (d.original_old z hz)
  exact h.trans (congrArg (fun a => [a]) he.symm)
theorem last_fixed_fiber {E : NormalForm P} (z : At d.K E) (hz : z.index ≠ d.x.index) :
    (TraceRoute.full d.last.route).fiber z = [d.newFixed z] := by
  have hk : z.index ≠ d.last.keep.index := by rw [d.last_keep]; exact hz
  have h := d.last.fixed_fiber z hk
  have he := d.last.fixed_unique z hk _ (d.original_last z)
  exact h.trans (congrArg (fun a => [a]) he.symm)
theorem inner_fixed_fiber {E : NormalForm P} (z : At d.K E) (hz : z.index ≠ d.x.index) :
    (TraceRoute.full d.inner.route).fiber (d.innerFixed z) = [d.original z hz] := by
  have h := d.inner.fixed_fiber (d.innerFixed z) (d.inner_fixed z hz)
  have he := d.inner.fixed_unique _ (d.inner_fixed z hz) _ (d.original_inner z hz)
  exact h.trans (congrArg (fun a => [a]) he.symm)

theorem other_old_fiber {E : NormalForm P} (z : At d.K E) (hz : z.index ≠ d.x.index) :
    d.oldTrace.fiber z = [d.original z hz] := by
  apply TraceRoute.fiber_single
  intro a
  constructor
  · intro ha
    rw [oldTrace,TraceRoute.get_ofMap] at ha
    cases hp : d.uParent a with
    | none => rw [hp] at ha; cases ha
    | some v =>
      obtain ⟨b,rfl,rfl⟩ := d.parent_original a v hp
      rw [d.u_prefix,Option.map_some,Option.some.injEq] at ha
      have he := d.s.original_unique z hz b
        ((d.s.square b).symm.trans ((congrArg d.outer.route.get (d.t_before b)).trans ha))
      exact congrArg (fun a => a.before [d.A,d.B]) he
  · intro he
    rw [he]
    rw [oldTrace,TraceRoute.get_ofMap]
    rw [d.original_parent,Option.map_some,d.original_old]
theorem other_new_fiber {E : NormalForm P} (z : At d.K E) (hz : z.index ≠ d.x.index) :
    d.newTrace.fiber z = [d.original z hz] :=
  (TraceRoute.fiber_ext _ _ _ _ (fun a => by rw [d.trace_square])).symm.trans (d.other_old_fiber z hz)
end DosenPetric.Reduced.Gentzen.SelectedLogical.Data
