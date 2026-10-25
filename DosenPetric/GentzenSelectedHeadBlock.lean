module

public import DosenPetric.GentzenLogicalRetainedFactor

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionBlock
universe u
variable {P : Type u} {F K : List (NormalForm P)}

abbrev selectedHead (d : ContractionBlock P F K) : ContractionBlock P (d.C::F) K where
  C := d.C
  gs := []::d.gs
  tail := d.tail
  upper := by change d.C::(repeated d.C d.gs++d.tail)=d.C::F; rw [d.upper]
  lower := d.lower

variable (d : ContractionBlock P F K)
theorem selectedHead_keep : d.selectedHead.keep=d.keep := by
  apply At.index_injective
  rw [keep_index,keep_index]
  rfl

theorem selectedHead_route : d.selectedHead.route=Route.cons d.keep d.route := by
  apply Route.ext_get
  intro A a
  apply At.index_injective
  cases a with
  | here =>
    rw [get_index,Route.get,keep_index]
    change copyIndex ([]::d.gs) 0=(gaps d.gs).length
    simp only [copyIndex,List.length_nil,Nat.not_lt_zero,ite_false,ite_true,Nat.zero_add]
  | there a =>
    rw [get_index,Route.get,get_index]
    change copyIndex ([]::d.gs) (a.index+1)=copyIndex d.gs a.index
    simp only [copyIndex,List.length_nil,Nat.not_lt_zero,ite_false,Nat.zero_add]
    rw [ite_eq_right (by omega : a.index+1≠0)]
    simp only [Nat.sub_zero,Nat.add_sub_cancel]

theorem selectedHead_selected : d.selectedHead.selected=
    .here d.C F::d.selected.map At.there := by
  apply At.list_index_injective
  rw [selected_indices]
  change copyOffsets ([]::d.gs)=List.map At.index (.here d.C F::List.map At.there d.selected)
  simp only [copyOffsets,List.length_nil,List.map_cons,List.map_map,At.index]
  rw [←d.selected_indices]
  simp only [List.map_map,Function.comp_def,At.index,Nat.zero_add,Nat.add_comm]

end DosenPetric.Reduced.Gentzen.ContractionBlock
