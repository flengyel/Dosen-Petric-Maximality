module

public import DosenPetric.GentzenContextSelectionNormalization
public import DosenPetric.GentzenLogicalEmbeddings

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionSelection
universe u
variable {P : Type u} {C : NormalForm P} {Γ Θ K : List (NormalForm P)}

theorem context_arity (g : SelectionMask C Γ) (t : SelectionMask C Θ) (M : List (NormalForm P))
    (p : ContractionSelection C (Γ++(M++Θ)) K) (h : p.mask=SelectionMask.contextMask g t M) :
    p.arity=g.count+t.count :=
  p.mask_count.symm.trans ((congrArg SelectionMask.count h).trans (SelectionMask.context_count g t M))

theorem context_selected_sum (g : SelectionMask C Γ) (t : SelectionMask C Θ) (M : List (NormalForm P))
    (p : ContractionSelection C (Γ++(M++Θ)) K) (h : p.mask=SelectionMask.contextMask g t M)
    (rho : At (Γ++(M++Θ)) C→Nat) :
    (p.selected.map rho).sum=(g.selected.map (fun a=>rho (a.before (M++Θ)))).sum+
      (t.selected.map (fun a=>rho (At.shift Γ (At.shift M a)))).sum := by
  have he:=p.mask_selected.symm.trans ((congrArg SelectionMask.selected h).trans
    (SelectionMask.context_selected g t M))
  rw [he,List.map_append,List.sum_append,List.map_map,List.map_map]
  rfl
end ContractionSelection

namespace FixedLogicalReducer
universe u
variable {P : Type u} {C : NormalForm P} {Γ Θ K L : List (NormalForm P)}
variable (g : SelectionMask C Γ) (t : SelectionMask C Θ) (A B D : NormalForm P)
variable (q : ContractionSelection C (Γ++D::Θ) K)
variable (p : ContractionSelection C (Γ++A::B::Θ) L)
variable (hq : q.mask=SelectionMask.contextMask g t [D])
variable (hp : p.mask=SelectionMask.contextMask g t [A,B])

include hq hp in
theorem context_sum_step (r0 : At (Γ++A::B::Θ) C→Nat) (r1 : At (Γ++D::Θ) C→Nat)
    (hfirst : ∀ a : At Γ C,r1 (a.before (D::Θ))=1+r0 (a.before (A::B::Θ)))
    (hlast : ∀ a : At Θ C,r1 (At.shift Γ a.there)=1+r0 (At.shift Γ a.there.there)) :
    (q.selected.map r1).sum=(p.selected.map r0).sum+q.arity := by
  have he0:=p.context_selected_sum g t [A,B] hp r0
  change (p.selected.map r0).sum=(g.selected.map (fun a=>r0 (a.before (A::B::Θ)))).sum+
    (t.selected.map (fun a=>r0 (At.shift Γ a.there.there))).sum at he0
  have he1:=q.context_selected_sum g t [D] hq r1
  have hm0 : g.selected.map (fun a=>r1 (a.before (D::Θ)))=
      g.selected.map (fun a=>1+r0 (a.before (A::B::Θ))) := by
    apply List.map_congr_left
    intro a _;exact hfirst a
  have hm1 : t.selected.map (fun a=>r1 (At.shift Γ a.there))=
      t.selected.map (fun a=>1+r0 (At.shift Γ a.there.there)) := by
    apply List.map_congr_left
    intro a _;exact hlast a
  change (q.selected.map r1).sum=(g.selected.map (fun a=>r1 (a.before (D::Θ)))).sum+
    (t.selected.map (fun a=>r1 (At.shift Γ a.there))).sum at he1
  rw [hm0,hm1,G.sum_map_one_add,G.sum_map_one_add,g.selected_count,t.selected_count] at he1
  have ha:=q.context_arity g t [D] hq
  omega
end FixedLogicalReducer
end DosenPetric.Reduced.Gentzen
