module

public import DosenPetric.GentzenSelectedSourceRepair
public import DosenPetric.GentzenContextSelectionSums

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.SelectedLogicalReducer
universe u
variable {P : Type u} {C : NormalForm P} {Γ Θ K L : List (NormalForm P)}
variable (g : SelectionMask C Γ) (t : SelectionMask C Θ)
variable (q : ContractionSelection C (Γ++C::Θ) K) (p : ContractionSelection C (Γ++Θ) L)
variable (hq : q.mask=SelectionMask.selectedContext g t) (hp : p.mask=g.append t)

include hq hp in
theorem selected_sum_step (r0 : At (Γ++Θ) C→Nat) (r1 : At (Γ++C::Θ) C→Nat)
    (hfirst : ∀ a : At Γ C,r1 (a.before (C::Θ))=1+r0 (a.before Θ))
    (hlast : ∀ a : At Θ C,r1 (At.shift Γ a.there)=1+r0 (At.shift Γ a))
    (hfresh : r1 (At.shift Γ (.here C Θ))=1) :
    (q.selected.map r1).sum=(p.selected.map r0).sum+q.arity := by
  have he0 : p.selected=g.selected.map (fun a=>a.before Θ)++t.selected.map (At.shift Γ) :=
    p.mask_selected.symm.trans ((congrArg SelectionMask.selected hp).trans
      (SelectionMask.append_selected g t))
  have he1 : q.selected=g.selected.map (fun a=>a.before (C::Θ))++
      (At.shift Γ (.here C Θ)::t.selected.map (fun a=>At.shift Γ a.there)) := by
    have h:=q.mask_selected.symm.trans (congrArg SelectionMask.selected hq)
    rw [SelectionMask.selectedContext,SelectionMask.append_selected] at h
    simpa only [SelectionMask.selected,List.map_cons,List.map_map,Function.comp_def] using h
  have hm0 : g.selected.map (fun a=>r1 (a.before (C::Θ)))=
      g.selected.map (fun a=>1+r0 (a.before Θ)) := by
    apply List.map_congr_left
    intro a _;exact hfirst a
  have hm1 : t.selected.map (fun a=>r1 (At.shift Γ a.there))=
      t.selected.map (fun a=>1+r0 (At.shift Γ a)) := by
    apply List.map_congr_left
    intro a _;exact hlast a
  have ha : q.arity=g.count+t.count+1 :=
    q.mask_count.symm.trans ((congrArg SelectionMask.count hq).trans (SelectionMask.selectedContext_count g t))
  simp only [he0,he1,List.map_append,List.map_cons,List.map_map,
    List.sum_append,List.sum_cons,Function.comp_def]
  rw [hm0,hm1,hfresh,G.sum_map_one_add,G.sum_map_one_add,g.selected_count,t.selected_count]
  omega

include hq hp in
theorem arity_balance : q.arity=p.arity+1 := by
  have h0:=p.mask_count
  have h1:=q.mask_count
  rw [hp,SelectionMask.append_count] at h0
  rw [hq,SelectionMask.selectedContext_count] at h1
  omega
end DosenPetric.Reduced.Gentzen.SelectedLogicalReducer
