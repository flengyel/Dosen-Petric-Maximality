module

public import DosenPetric.GentzenSourceLogicalBlocked

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionSelection
universe u
variable {P : Type u} {C : NormalForm P} {F K U L : List (NormalForm P)}
variable (p : ContractionSelection C F K) (q : ContractionSelection C U L)

theorem retain_keep : (p.retainChain q).keep=At.shift p.erased q.keep := by
  induction p with
  | last Θ => exact q.prepend_keep Θ
  | fixed A p ih => exact congrArg At.there ih
  | more p ih => exact ih

def sourceKeep : At (p.erased++(q.erased++[C])) C :=
  At.shift p.erased (At.shift q.erased (.here C []))

theorem sourceOld_keep : (p.sourceOld q).keep=p.sourceKeep q := by
  rw [sourceOld,keep_cast,chain_keep,chain_keep]
  rfl

theorem sourceRetained_keep : (p.sourceRetained q).keep=p.sourceKeep q := by
  rw [sourceRetained,keep_cast,retain_keep,retain_keep]
  rfl

theorem sourceOld_selected : (p.sourceOld q).selected=
    p.selected.map (fun a => (a.before U).before [C])++
    (q.selected.map (fun a => (At.shift F a).before [C])++
      [At.shift (F++U) (.here C [])]) := by
  apply At.list_index_injective
  rw [sourceOld,selected_cast,chain_selected,chain_selected]
  simp only [selected,List.map_append,List.map_cons,List.map_nil,List.map_map,
    Function.comp_def,At.index_cast,At.index_before,At.index_shift,At.index,List.length_append,Nat.add_zero]

theorem sourceRetained_selected : (p.sourceRetained q).selected=
    [(p.keep.before L).before [C],(At.shift K q.keep).before [C],
      At.shift (K++L) (.here C [])] := by
  apply At.list_index_injective
  rw [sourceRetained,selected_cast,retain_selected,retain_selected]
  simp only [selected,List.map_cons,List.map_nil,At.index_cast,At.index_before,At.index_shift,At.index,
    List.length_append,Nat.add_zero]

end DosenPetric.Reduced.Gentzen.ContractionSelection
