module

public import DosenPetric.GentzenContractionPrepend
public import DosenPetric.GentzenSingleMixFibers

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.OtherMix
universe u
variable {P : Type u} {F K : List (NormalForm P)}
variable (d : ContractionBlock P F K) (hn : 2 ≤ d.gs.length) (Ξ : List (NormalForm P))
def oldG : TraceRoute (Ξ++K) F := TraceRoute.ofMap _ _ (fun a => some ((d.prepend hn Ξ).route.get (At.shift Ξ a)))
def newG (d : ContractionBlock P F K) (_hn : 2 ≤ d.gs.length) (Ξ : List (NormalForm P)) :
    TraceRoute (Ξ++K) F := TraceRoute.ofMap _ _ (fun a => some (At.shift Ξ (d.route.get a)))
def oldF : TraceRoute (Ξ++K) Ξ := TraceRoute.ofMap _ _ (fun a => some ((d.prepend hn Ξ).route.get (a.before F)))
def newF (_d : ContractionBlock P F K) (_hn : 2 ≤ _d.gs.length) (Ξ : List (NormalForm P)) :
    TraceRoute (Ξ++K) Ξ := TraceRoute.before Ξ K
theorem squareG : oldG d hn Ξ = newG d hn Ξ := by
  apply TraceRoute.ext
  intro A a
  simp only [oldG,newG,TraceRoute.get_ofMap,d.prepend_shift]
theorem squareF : oldF d hn Ξ = newF d hn Ξ := by
  apply TraceRoute.ext
  intro A a
  simp only [oldF,newF,TraceRoute.before,TraceRoute.get_ofMap,d.prepend_before]
theorem fiberG_suffix {A : NormalForm P} (z : At K A) :
    (newG d hn Ξ).fiber (At.shift Ξ z) = (TraceRoute.full d.route).fiber z := by
  apply TraceRoute.fiber_ext
  intro a
  rw [newG,TraceRoute.get_ofMap,TraceRoute.get_full,Option.some.injEq,Option.some.injEq]
  exact ⟨At.shift_injective Ξ _ _,fun h => congrArg (At.shift Ξ) h⟩
theorem fiberF_suffix {A : NormalForm P} (z : At K A) :
    (newF d hn Ξ).fiber (At.shift Ξ z) = [] := by
  rw [newF,TraceRoute.fiber_before,At.splitAppend_shift]
theorem fiberG_prefix {A : NormalForm P} (z : At Ξ A) :
    (newG d hn Ξ).fiber (z.before K) = [] := by
  apply TraceRoute.fiber_empty
  intro a h
  rw [newG,TraceRoute.get_ofMap,Option.some.injEq] at h
  exact At.before_ne_shift _ _ h.symm
theorem fiberF_prefix {A : NormalForm P} (z : At Ξ A) :
    (newF d hn Ξ).fiber (z.before K) = [z] := by
  rw [newF,TraceRoute.fiber_before,At.splitAppend_before]
theorem retained_fibers :
    (newG d hn Ξ).fiber (At.shift Ξ d.keep) = d.selected ∧
    (newF d hn Ξ).fiber (At.shift Ξ d.keep) = [] :=
  ⟨(fiberG_suffix d hn Ξ _).trans d.selected_fiber,fiberF_suffix d hn Ξ _⟩
theorem fixed_fibers {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) :
    (newG d hn Ξ).fiber (At.shift Ξ z) = [d.fixed z hz] ∧
    (newF d hn Ξ).fiber (At.shift Ξ z) = [] :=
  ⟨(fiberG_suffix d hn Ξ _).trans (d.fixed_fiber z hz),fiberF_suffix d hn Ξ _⟩
theorem old_retained_fibers :
    (oldG d hn Ξ).fiber (At.shift Ξ d.keep) = d.selected ∧
    (oldF d hn Ξ).fiber (At.shift Ξ d.keep) = [] := by
  rw [squareG,squareF]
  exact retained_fibers d hn Ξ
theorem old_fixed_fibers {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) :
    (oldG d hn Ξ).fiber (At.shift Ξ z) = [d.fixed z hz] ∧
    (oldF d hn Ξ).fiber (At.shift Ξ z) = [] := by
  rw [squareG,squareF]
  exact fixed_fibers d hn Ξ z hz
theorem old_prefix_fibers {A : NormalForm P} (z : At Ξ A) :
    (oldG d hn Ξ).fiber (z.before K) = [] ∧ (oldF d hn Ξ).fiber (z.before K) = [z] := by
  rw [squareG,squareF]
  exact ⟨fiberG_prefix d hn Ξ z,fiberF_prefix d hn Ξ z⟩
theorem selected_transport : (d.prepend hn Ξ).selected = d.selected.map (At.shift Ξ) :=
  d.prepend_selected hn Ξ
theorem selected_length : (d.prepend hn Ξ).selected.length = d.gs.length :=
  (d.prepend hn Ξ).selected_length.trans (d.prepend_count hn Ξ)
theorem selected_from_g (a : At (Ξ++F) d.C) (ha : a ∈ (d.prepend hn Ξ).selected) :
    ∃ b, b ∈ d.selected ∧ a = At.shift Ξ b := by
  rw [selected_transport,List.mem_map] at ha
  obtain ⟨b,hb,he⟩ := ha
  exact ⟨b,hb,he.symm⟩
theorem f_not_selected (a : At Ξ d.C) : a.before F ∉ (d.prepend hn Ξ).selected := by
  intro h
  obtain ⟨b,_,hb⟩ := selected_from_g d hn Ξ _ h
  exact At.before_ne_shift a b hb
theorem retained_index : (At.shift Ξ d.keep).index = Ξ.length+(gaps d.gs).length := by
  rw [At.index_shift,d.keep_index]
theorem prefix_fixed {A : NormalForm P} (a : At Ξ A) :
    (a.before K).index ≠ (d.prepend hn Ξ).keep.index := by
  rw [d.prepend_keep,At.index_before,At.index_shift]
  have h := a.index_lt
  omega
theorem suffix_fixed {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) :
    (At.shift Ξ z).index ≠ (d.prepend hn Ξ).keep.index := by
  rw [d.prepend_keep,At.index_shift,At.index_shift]
  omega
theorem outer_retained_fiber :
    (TraceRoute.full (d.prepend hn Ξ).route).fiber (At.shift Ξ d.keep) =
      d.selected.map (At.shift Ξ) := by
  rw [← d.prepend_keep hn Ξ]
  exact (d.prepend hn Ξ).selected_fiber.trans (d.prepend_selected hn Ξ)
theorem outer_fixed_fiber {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) :
    (TraceRoute.full (d.prepend hn Ξ).route).fiber (At.shift Ξ z) = [At.shift Ξ (d.fixed z hz)] := by
  have h := (d.prepend hn Ξ).fixed_fiber _ (suffix_fixed d hn Ξ z hz)
  have he := (d.prepend hn Ξ).fixed_unique _ (suffix_fixed d hn Ξ z hz) (At.shift Ξ (d.fixed z hz))
    ((d.prepend_shift hn Ξ _).trans (congrArg (At.shift Ξ) (d.fixed_get z hz)))
  exact h.trans (congrArg (fun a => [a]) he.symm)
theorem outer_prefix_fiber {A : NormalForm P} (z : At Ξ A) :
    (TraceRoute.full (d.prepend hn Ξ).route).fiber (z.before K) = [z.before F] := by
  have h := (d.prepend hn Ξ).fixed_fiber _ (prefix_fixed d hn Ξ z)
  have he := (d.prepend hn Ξ).fixed_unique _ (prefix_fixed d hn Ξ z) (z.before F) (d.prepend_before hn Ξ z)
  exact h.trans (congrArg (fun a => [a]) he.symm)
end DosenPetric.Reduced.Gentzen.OtherMix
