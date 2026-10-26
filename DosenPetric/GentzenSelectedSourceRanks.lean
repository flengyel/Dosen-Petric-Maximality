module

public import DosenPetric.GentzenSelectedLogicalSums

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.SelectedLogicalReducer
universe u
variable {P : Type u} {A B : NormalForm P} {F L Δ Γ Θ : List (NormalForm P)}

theorem sourceInnerL_formula (p : ContractionSelection (.conj A B) F L) (f : G P (F++[A,B]) Δ) :
    sourceInnerL p f=(p.selected.map (fun a=>f.rho .left (a.before [A,B]))).sum+
      (if 2≤p.arity then 1 else 0) := by
  let rf : At (F++[A,B]) (.conj A B)→Nat:=f.rho .left
  have h:=(sourceInnerL_eq p f).trans ((p.extend [A,B]).performL_rank Δ f)
  change sourceInnerL p f=((p.extend [A,B]).selected.map rf).sum+_ at h
  rw [p.extend_selected,List.map_map,p.extend_arity] at h
  exact h

theorem sourceInner_moveL (p : ContractionSelection (.conj A B) (Γ++Θ) L)
    (f : G P (Γ++A::B::Θ) Δ) :
    sourceInnerL p (G.moveEndL Γ [A,B] Θ Δ f)=
      (p.selected.map (fun a=>f.rho .left (At.reinsert Γ Θ [A,B] a))).sum+p.arity+
        (if 2≤p.arity then 1 else 0) := by
  let ft:=G.moveEndL Γ [A,B] Θ Δ f
  let rt : At ((Γ++Θ)++[A,B]) (.conj A B)→Nat:=ft.rho .left
  let r0 : At (Γ++Θ) (.conj A B)→Nat:=fun a=>f.rho .left (At.reinsert Γ Θ [A,B] a)
  have hm : p.selected.map (fun a=>rt (a.before [A,B]))=p.selected.map (fun a=>1+r0 a) := by
    apply List.map_congr_left
    intro a _
    have h0:=G.moveEndL_rank Γ [A,B] Θ Δ f (At.reinsert Γ Θ [A,B] a)
    have he:=congrArg rt (At.moveEnd_reinsert Γ Θ [A,B] a)
    exact he.symm.trans h0
  have h:=sourceInnerL_formula p ft
  change sourceInnerL p ft=(p.selected.map (fun a=>rt (a.before [A,B]))).sum+_ at h
  rw [hm,G.sum_map_one_add,p.selected_length] at h
  change sourceInnerL p ft=(p.selected.map r0).sum+p.arity+_
  omega

theorem sourceInnerR_formula (p : ContractionSelection (.disj A B) F L) (f : G P Δ (F++[A,B])) :
    sourceInnerR p f=(p.selected.map (fun a=>f.rho .right (a.before [A,B]))).sum+
      (if 2≤p.arity then 1 else 0) := by
  let rf : At (F++[A,B]) (.disj A B)→Nat:=f.rho .right
  have h:=(sourceInnerR_eq p f).trans ((p.extend [A,B]).performR_rank Δ f)
  change sourceInnerR p f=((p.extend [A,B]).selected.map rf).sum+_ at h
  rw [p.extend_selected,List.map_map,p.extend_arity] at h
  exact h

theorem sourceInner_moveR (p : ContractionSelection (.disj A B) (Γ++Θ) L)
    (f : G P Δ (Γ++A::B::Θ)) :
    sourceInnerR p (G.moveEndR Δ Γ [A,B] Θ f)=
      (p.selected.map (fun a=>f.rho .right (At.reinsert Γ Θ [A,B] a))).sum+p.arity+
        (if 2≤p.arity then 1 else 0) := by
  let ft:=G.moveEndR Δ Γ [A,B] Θ f
  let rt : At ((Γ++Θ)++[A,B]) (.disj A B)→Nat:=ft.rho .right
  let r0 : At (Γ++Θ) (.disj A B)→Nat:=fun a=>f.rho .right (At.reinsert Γ Θ [A,B] a)
  have hm : p.selected.map (fun a=>rt (a.before [A,B]))=p.selected.map (fun a=>1+r0 a) := by
    apply List.map_congr_left
    intro a _
    have h0:=G.moveEndR_rank Δ Γ [A,B] Θ f (At.reinsert Γ Θ [A,B] a)
    have he:=congrArg rt (At.moveEnd_reinsert Γ Θ [A,B] a)
    exact he.symm.trans h0
  have h:=sourceInnerR_formula p ft
  change sourceInnerR p ft=(p.selected.map (fun a=>rt (a.before [A,B]))).sum+_ at h
  rw [hm,G.sum_map_one_add,p.selected_length] at h
  change sourceInnerR p ft=(p.selected.map r0).sum+p.arity+_
  omega
end DosenPetric.Reduced.Gentzen.SelectedLogicalReducer
