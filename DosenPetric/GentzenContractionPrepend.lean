module

public import DosenPetric.GentzenContractionSelectionCoordinates
public import DosenPetric.GentzenContractionAppend

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionSelection
variable {C : NormalForm P} {F K : List (NormalForm P)} (p : ContractionSelection C F K)
theorem prepend_before (Ξ : List (NormalForm P)) {A : NormalForm P} (a : At Ξ A) :
    (p.prependFixed Ξ).route.get (a.before F) = a.before K := by
  induction Ξ with
  | nil => cases a
  | cons B Ξ ih =>
    cases a with
    | here => rfl
    | there a =>
      simpa only [prependFixed,route,Route.get,Route.get_map,At.before] using congrArg At.there (ih a)
theorem prepend_shift (Ξ : List (NormalForm P)) {A : NormalForm P} (a : At F A) :
    (p.prependFixed Ξ).route.get (At.shift Ξ a) = At.shift Ξ (p.route.get a) := by
  induction Ξ with
  | nil => rfl
  | cons B Ξ ih =>
    simpa only [prependFixed,route,Route.get,Route.get_map,At.shift] using congrArg At.there ih
theorem prepend_keep (Ξ : List (NormalForm P)) :
    (p.prependFixed Ξ).keep = At.shift Ξ p.keep := by
  induction Ξ with
  | nil => rfl
  | cons B Ξ ih => exact congrArg At.there ih
theorem prepend_selected (Ξ : List (NormalForm P)) :
    (p.prependFixed Ξ).selected = p.selected.map (At.shift Ξ) := by
  induction Ξ with
  | nil => exact (List.map_id ..).symm
  | cons B Ξ ih =>
    simp only [prependFixed,selected,ih,List.map_map]
    rfl
theorem prepend_count (Ξ : List (NormalForm P)) :
    (p.prependFixed Ξ).gs.length = p.gs.length := by
  change ((p.prependFixed Ξ).first::(p.prependFixed Ξ).rest).length = (p.first::p.rest).length
  rw [rest_prependFixed]
  rfl
end ContractionSelection

namespace ContractionBlock
variable {F K : List (NormalForm P)} (d : ContractionBlock P F K) (hn : 2 ≤ d.gs.length)
include hn
theorem nonempty : d.gs ≠ [] := by
  intro he
  rw [he] at hn
  exact Nat.not_succ_le_zero 1 hn
abbrev prepend (Ξ : List (NormalForm P)) : ContractionBlock P (Ξ++F) (Ξ++K) :=
  ((d.selection (d.nonempty hn)).prependFixed Ξ).block
theorem selection_route : (d.selection (d.nonempty hn)).route = d.route :=
  (d.selection (d.nonempty hn)).route_eq.trans (congrArg ContractionBlock.route (d.selection_block _))
theorem selection_keep : (d.selection (d.nonempty hn)).keep = d.keep := by
  apply At.index_injective
  rw [ContractionSelection.keep_index,d.keep_index]
  exact congrArg (fun b => (gaps b.gs).length) (d.selection_block _)
theorem selection_selected : (d.selection (d.nonempty hn)).selected = d.selected := by
  apply At.list_index_injective
  exact (congrArg (List.map At.index) (d.selection (d.nonempty hn)).selected_eq).trans
    ((d.selection (d.nonempty hn)).block.selected_indices.trans
      ((congrArg (fun b => copyOffsets b.gs) (d.selection_block _)).trans d.selected_indices.symm))
theorem prepend_count (Ξ : List (NormalForm P)) : (d.prepend hn Ξ).gs.length = d.gs.length :=
  ((d.selection (d.nonempty hn)).prepend_count Ξ).trans
    (congrArg (fun b => b.gs.length) (d.selection_block _))
theorem prepend_bound (Ξ : List (NormalForm P)) : 2 ≤ (d.prepend hn Ξ).gs.length := by
  rw [d.prepend_count hn Ξ]
  exact hn
theorem prepend_tail (Ξ : List (NormalForm P)) : (d.prepend hn Ξ).tail = d.tail := by
  change ((d.selection (d.nonempty hn)).prependFixed Ξ).tail = d.tail
  exact (ContractionSelection.tail_prependFixed Ξ _).trans
    (congrArg ContractionBlock.tail (d.selection_block _))
theorem prepend_before (Ξ : List (NormalForm P)) {A : NormalForm P} (a : At Ξ A) :
    (d.prepend hn Ξ).route.get (a.before F) = a.before K := by
  rw [← ContractionSelection.route_eq]
  exact (d.selection (d.nonempty hn)).prepend_before Ξ a
theorem prepend_shift (Ξ : List (NormalForm P)) {A : NormalForm P} (a : At F A) :
    (d.prepend hn Ξ).route.get (At.shift Ξ a) = At.shift Ξ (d.route.get a) := by
  rw [← ContractionSelection.route_eq]
  exact ((d.selection (d.nonempty hn)).prepend_shift Ξ a).trans
    (congrArg (fun w : Route K F => At.shift Ξ (w.get a)) (d.selection_route hn))
theorem prepend_keep (Ξ : List (NormalForm P)) :
    (d.prepend hn Ξ).keep = At.shift Ξ d.keep := by
  exact (ContractionSelection.keep_eq _).symm.trans
    (((d.selection (d.nonempty hn)).prepend_keep Ξ).trans
      (congrArg (At.shift Ξ) (d.selection_keep hn)))
theorem prepend_selected (Ξ : List (NormalForm P)) :
    (d.prepend hn Ξ).selected = d.selected.map (At.shift Ξ) := by
  exact (ContractionSelection.selected_eq _).symm.trans
    (((d.selection (d.nonempty hn)).prepend_selected Ξ).trans
      (congrArg (List.map (At.shift Ξ)) (d.selection_selected hn)))
theorem prepend_gaps (Ξ H : List (NormalForm P)) (hs : List (List (NormalForm P)))
    (hg : d.gs = H::hs) : (d.prepend hn Ξ).gs = (Ξ++H)::hs := by
  let p := d.selection (d.nonempty hn)
  have he : p.first::p.rest = H::hs :=
    (congrArg ContractionBlock.gs (d.selection_block _)).trans hg
  have hf := List.cons.inj he
  change (p.prependFixed Ξ).first::(p.prependFixed Ξ).rest = _
  rw [ContractionSelection.first_prependFixed,ContractionSelection.rest_prependFixed,hf.1,hf.2]
end ContractionBlock
end DosenPetric.Reduced.Gentzen
