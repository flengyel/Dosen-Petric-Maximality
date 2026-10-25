module

public import DosenPetric.GentzenParametricConjunction

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionSelection
universe u
variable {P : Type u} {C : NormalForm P} {F K : List (NormalForm P)}

abbrev retainedHeadBlock (p : ContractionSelection C F K) : ContractionBlock P (C::K) K where
  C := C
  gs := [[],gaps p.gs]
  tail := p.tail
  upper := by
    simpa only [repeated,List.nil_append,List.cons_append,List.append_assoc] using congrArg (List.cons C) p.lower
  lower := by simpa only [gaps,List.nil_append,List.append_nil] using p.lower

variable (p : ContractionSelection C F K)
theorem retainedHead_eq : p.retainedHeadBlock=p.retained.block.selectedHead := by
  apply ContractionBlock.ext_data
  · rfl
  · change [[],gaps p.gs]=[]::p.retained.gs
    rw [p.retained_gs]
  · exact p.retained_tail.symm

theorem retainedHead_keep : p.retainedHeadBlock.keep=p.keep := by
  apply At.index_injective
  rw [ContractionBlock.keep_index,p.keep_index]
  simp only [gaps,List.nil_append,List.append_nil]

theorem retainedHead_route : p.retainedHeadBlock.route=Route.cons p.keep (Route.identity K) := by
  rw [p.retainedHead_eq,ContractionBlock.selectedHead_route,←p.retained.route_eq,p.retained_route]
  rw [←p.retained.keep_eq,p.retained_keep]

theorem retainedHead_selected : p.retainedHeadBlock.selected=[.here C K,.there p.keep] := by
  apply At.list_index_injective
  rw [ContractionBlock.selected_indices]
  simp only [retainedHeadBlock,copyOffsets,List.length_nil,List.map_cons,List.map_nil,At.index,p.keep_index,Nat.zero_add,Nat.add_comm]

theorem retainedHead_square (o : Op) :
    (more p).route.sideArrow o=(side P o).comp (p.retainedHeadBlock.route.sideArrow o)
      ((p.route.head C).sideArrow o) := by
  apply side_ext o
  intro A a
  rw [(side P o).assoc,Route.sideArrow_get,Route.sideArrow_get,Route.sideArrow_get,p.retainedHead_route]
  apply congrArg (component o)
  cases a with
  | here => rfl
  | there a =>
    simp only [route,Route.head,Route.get,Route.get_map,Route.get_identity]

end DosenPetric.Reduced.Gentzen.ContractionSelection
