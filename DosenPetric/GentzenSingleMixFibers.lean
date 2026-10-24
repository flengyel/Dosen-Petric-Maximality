module

public import DosenPetric.GentzenContractionAppend

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace At
theorem before_injective {Γ : List (NormalForm P)} (Ξ : List (NormalForm P))
    {A : NormalForm P} (a b : At Γ A) (h : a.before Ξ = b.before Ξ) : a = b := by
  have he := congrArg (At.splitAppend Γ Ξ) h
  simpa only [At.splitAppend_before,Sum.inl.injEq] using he
theorem shift_injective (Γ : List (NormalForm P)) {Ξ : List (NormalForm P)}
    {A : NormalForm P} (a b : At Ξ A) (h : At.shift Γ a = At.shift Γ b) : a = b := by
  have he := congrArg (At.splitAppend Γ Ξ) h
  simpa only [At.splitAppend_shift,Sum.inr.injEq] using he
theorem before_ne_shift {Γ Ξ : List (NormalForm P)} {A : NormalForm P}
    (a : At Γ A) (b : At Ξ A) : a.before Ξ ≠ At.shift Γ b := by
  intro h
  have he := congrArg (At.splitAppend Γ Ξ) h
  rw [At.splitAppend_before,At.splitAppend_shift] at he
  cases he
end At

namespace SingleMix
variable {F K : List (NormalForm P)} (d : ContractionBlock P F K) (Ξ : List (NormalForm P))
def oldG : TraceRoute (K++Ξ) F := TraceRoute.ofMap _ _ (fun a => some ((d.extend Ξ).route.get (a.before Ξ)))
def newG : TraceRoute (K++Ξ) F := TraceRoute.ofMap _ _ (fun a => some ((d.route.get a).before Ξ))
def oldF : TraceRoute (K++Ξ) Ξ := TraceRoute.ofMap _ _ (fun a => some ((d.extend Ξ).route.get (At.shift F a)))
def newF (_d : ContractionBlock P F K) (Ξ : List (NormalForm P)) : TraceRoute (K++Ξ) Ξ := TraceRoute.shift K Ξ
theorem squareG : oldG d Ξ = newG d Ξ := by
  apply TraceRoute.ext
  intro A a
  simp only [oldG,newG,TraceRoute.get_ofMap,d.extend_before]
theorem squareF : oldF d Ξ = newF d Ξ := by
  apply TraceRoute.ext
  intro A a
  simp only [oldF,newF,TraceRoute.shift,TraceRoute.get_ofMap,d.extend_shift]
theorem fiberG_before {A : NormalForm P} (z : At K A) :
    (newG d Ξ).fiber (z.before Ξ) = (TraceRoute.full d.route).fiber z := by
  apply TraceRoute.fiber_ext
  intro a
  rw [newG,TraceRoute.get_ofMap,TraceRoute.get_full,Option.some.injEq,Option.some.injEq]
  exact ⟨At.before_injective Ξ _ _,fun h => congrArg (fun a : At K A => a.before Ξ) h⟩
theorem fiberF_before {A : NormalForm P} (z : At K A) :
    (newF d Ξ).fiber (z.before Ξ) = [] := by
  rw [newF,TraceRoute.fiber_shift,At.splitAppend_before]
theorem fiberG_shift {A : NormalForm P} (z : At Ξ A) :
    (newG d Ξ).fiber (At.shift K z) = [] := by
  apply TraceRoute.fiber_empty
  intro a h
  rw [newG,TraceRoute.get_ofMap,Option.some.injEq] at h
  exact At.before_ne_shift _ _ h
theorem fiberF_shift {A : NormalForm P} (z : At Ξ A) :
    (newF d Ξ).fiber (At.shift K z) = [z] := by
  rw [newF,TraceRoute.fiber_shift,At.splitAppend_shift]
theorem retained_fibers :
    (newG d Ξ).fiber (d.keep.before Ξ) = d.selected ∧
    (newF d Ξ).fiber (d.keep.before Ξ) = [] :=
  ⟨(fiberG_before d Ξ _).trans d.selected_fiber,fiberF_before d Ξ _⟩
theorem fixed_fibers {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) :
    (newG d Ξ).fiber (z.before Ξ) = [d.fixed z hz] ∧
    (newF d Ξ).fiber (z.before Ξ) = [] :=
  ⟨(fiberG_before d Ξ _).trans (d.fixed_fiber z hz),fiberF_before d Ξ _⟩
theorem old_retained_fibers :
    (oldG d Ξ).fiber (d.keep.before Ξ) = d.selected ∧
    (oldF d Ξ).fiber (d.keep.before Ξ) = [] := by
  rw [squareG,squareF]
  exact retained_fibers d Ξ
theorem old_fixed_fibers {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) :
    (oldG d Ξ).fiber (z.before Ξ) = [d.fixed z hz] ∧
    (oldF d Ξ).fiber (z.before Ξ) = [] := by
  rw [squareG,squareF]
  exact fixed_fibers d Ξ z hz
theorem old_suffix_fibers {A : NormalForm P} (z : At Ξ A) :
    (oldG d Ξ).fiber (At.shift K z) = [] ∧ (oldF d Ξ).fiber (At.shift K z) = [z] := by
  rw [squareG,squareF]
  exact ⟨fiberG_shift d Ξ z,fiberF_shift d Ξ z⟩
theorem selected_transport : (d.extend Ξ).selected = d.selected.map (fun a => a.before Ξ) :=
  d.extend_selected Ξ
theorem selected_length : (d.extend Ξ).selected.length = d.gs.length :=
  (d.extend Ξ).selected_length
theorem selected_from_g (a : At (F++Ξ) d.C) (ha : a ∈ (d.extend Ξ).selected) :
    ∃ b, b ∈ d.selected ∧ a = b.before Ξ := by
  rw [selected_transport,List.mem_map] at ha
  obtain ⟨b,hb,he⟩ := ha
  exact ⟨b,hb,he.symm⟩
theorem f_not_selected (a : At Ξ d.C) : At.shift F a ∉ (d.extend Ξ).selected := by
  intro h
  obtain ⟨b,_,hb⟩ := selected_from_g d Ξ _ h
  exact At.before_ne_shift b a hb.symm
theorem retained_index : (d.keep.before Ξ).index = (gaps d.gs).length := by
  rw [At.index_before,d.keep_index]
theorem suffix_fixed {A : NormalForm P} (a : At Ξ A) :
    (At.shift K a).index ≠ (d.extend Ξ).keep.index := by
  rw [d.extend_keep,At.index_before,At.index_shift]
  have h := d.keep.index_lt
  omega
theorem prefix_fixed {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) :
    (z.before Ξ).index ≠ (d.extend Ξ).keep.index := by
  rw [d.extend_keep,At.index_before,At.index_before]
  exact hz
theorem outer_retained_fiber :
    (TraceRoute.full (d.extend Ξ).route).fiber (d.keep.before Ξ) =
      d.selected.map (fun a => a.before Ξ) := by
  rw [← d.extend_keep]
  exact (d.extend Ξ).selected_fiber.trans (d.extend_selected Ξ)
theorem outer_fixed_fiber {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) :
    (TraceRoute.full (d.extend Ξ).route).fiber (z.before Ξ) = [(d.fixed z hz).before Ξ] := by
  have h := (d.extend Ξ).fixed_fiber (z.before Ξ) (prefix_fixed d Ξ z hz)
  have he := (d.extend Ξ).fixed_unique _ (prefix_fixed d Ξ z hz) ((d.fixed z hz).before Ξ)
    ((d.extend_before Ξ _).trans (congrArg (fun a => a.before Ξ) (d.fixed_get z hz)))
  exact h.trans (congrArg (fun a => [a]) he.symm)
theorem outer_suffix_fiber {A : NormalForm P} (z : At Ξ A) :
    (TraceRoute.full (d.extend Ξ).route).fiber (At.shift K z) = [At.shift F z] := by
  have h := (d.extend Ξ).fixed_fiber _ (suffix_fixed d Ξ z)
  have he := (d.extend Ξ).fixed_unique _ (suffix_fixed d Ξ z) (At.shift F z) (d.extend_shift Ξ z)
  exact h.trans (congrArg (fun a => [a]) he.symm)
end SingleMix
end DosenPetric.Reduced.Gentzen
