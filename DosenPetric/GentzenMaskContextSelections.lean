module

public import DosenPetric.GentzenMaskLogicalNaturality

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.SelectionMask
universe u
variable {P : Type u} {C : NormalForm P} {F U Γ Θ : List (NormalForm P)}

theorem append_selected (m : SelectionMask C F) (n : SelectionMask C U) :
    (m.append n).selected=m.selected.map (fun a=>a.before U)++n.selected.map (At.shift F) := by
  induction m with
  | nil=>
    simp only [append,selected,List.map_nil,List.nil_append,At.shift]
    exact (List.map_id n.selected).symm
  | fixed A m ih=>
    simp only [append,selected,ih,List.map_append,List.map_map,Function.comp_def]
    rfl
  | pick m ih=>
    simp only [append,selected,ih,List.map_append,List.map_cons,List.map_map,Function.comp_def]
    rfl

theorem context_count (g : SelectionMask C Γ) (t : SelectionMask C Θ) (M : List (NormalForm P)) :
    (contextMask g t M).count=g.count+t.count := by
  simp only [contextMask,append_count,allFixed_count,Nat.zero_add]

theorem context_selected (g : SelectionMask C Γ) (t : SelectionMask C Θ) (M : List (NormalForm P)) :
    (contextMask g t M).selected=
      g.selected.map (fun a=>a.before (M++Θ))++t.selected.map (fun a=>At.shift Γ (At.shift M a)) := by
  simp only [contextMask,append_selected,allFixed_selected,List.map_nil,List.nil_append,List.map_map,Function.comp_def]
end DosenPetric.Reduced.Gentzen.SelectionMask
