module

public import DosenPetric.GentzenExchangeFactor
public import DosenPetric.GentzenRouteFiberSums
public import DosenPetric.GentzenSelectionRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.UnrestrictedExchange
universe u
variable {P : Type u} {C : NormalForm P} {Γ X Y Θ K K0 : List (NormalForm P)}
variable (q : ContractionSelection C (Γ++Y++X++Θ) K)
variable (p : ContractionSelection C (Γ++X++Y++Θ) K0) (r : ExchangeScript P K K0)
variable (hk : r.get p.keep=q.keep)
variable (hs : ∀ {A : NormalForm P} (a : At (Γ++X++Y++Θ) A),
  q.route.get (a.swapBlocks Γ X Y Θ)=r.get (p.route.get a))

include hk hs

omit hk in
theorem square (o : Op) :
    (side P o).comp (q.route.sideArrow o) (exchangeBack o Γ X Y Θ)=
      (side P o).comp (r.arrow o) (p.route.sideArrow o) := by
  apply side_ext o
  intro A a
  rw [(side P o).assoc,exchangeBack_component,Route.sideArrow_get,
    (side P o).assoc,Route.sideArrow_get,r.component,hs]

theorem selected_perm :
    List.Perm (p.selected.map (fun a=>a.swapBlocks Γ X Y Θ)) q.selected := by
  have hn : (p.selected.map (fun a=>a.swapBlocks Γ X Y Θ)).Nodup := by
    apply List.pairwise_map.mpr
    apply p.selected_ordered.imp
    intro a b hab he
    have hh:=At.swapBlocks_injective Γ X Y Θ a b he
    cases hh;omega
  have hq : q.selected.Nodup := by
    apply q.selected_ordered.imp
    intro a b hab he
    cases he;omega
  apply (List.perm_ext_iff_of_nodup hn hq).mpr
  intro a
  constructor
  · intro h
    obtain ⟨b,hb,he⟩:=List.mem_map.mp h
    rw [←he,q.selected_iff,hs,←hk]
    exact congrArg r.get ((p.selected_iff b).mp hb)
  · intro ha
    let b:=a.swapBlocks Γ Y X Θ
    have he : b.swapBlocks Γ X Y Θ=a:=At.swapBlocks_inverse Γ Y X Θ a
    apply List.mem_map.mpr
    refine ⟨b,?_,he⟩
    apply (p.selected_iff b).mpr
    apply r.injective
    rw [hk,←hs,he]
    exact (q.selected_iff a).mp ha

theorem old_rankL {Δ : List (NormalForm P)} (t : G P (Γ++X++Y++Θ) Δ)
    (hn : 2≤q.arity) :
    (q.performL Δ (G.exchangeL Γ X Y Θ Δ t)).rho .left q.keep=
      (p.selected.map (fun a=>t.rho .left a)).sum+p.arity+1 := by
  have he:=((selected_perm q p r hk hs).map
    (fun (a : At (Γ++Y++X++Θ) C)=>(G.exchangeL Γ X Y Θ Δ t).rho .left a)).sum_nat
  rw [List.map_map] at he
  let R : At K C→Nat := (q.performL Δ (G.exchangeL Γ X Y Θ Δ t)).rho .left
  have hh:=q.performL_rank Δ (G.exchangeL Γ X Y Θ Δ t)
  change R q.keep=(q.selected.map (fun (a : At (Γ++Y++X++Θ) C)=>(G.exchangeL Γ X Y Θ Δ t).rho .left a)).sum+_ at hh
  change R q.keep=_
  rw [ite_eq_left hn,←he] at hh
  simp only [Function.comp_def,G.rho_exchangeL_embedded] at hh
  let rt : At (Γ++X++Y++Θ) C→Nat := t.rho .left
  change R q.keep=(p.selected.map (fun a=>1+rt a)).sum+1 at hh
  change R q.keep=(p.selected.map rt).sum+p.arity+1
  rw [G.sum_map_one_add,p.selected_length] at hh
  omega

theorem old_rankR {Δ : List (NormalForm P)} (t : G P Δ (Γ++X++Y++Θ))
    (hn : 2≤q.arity) :
    (q.performR Δ (G.exchangeR Δ Γ X Y Θ t)).rho .right q.keep=
      (p.selected.map (fun a=>t.rho .right a)).sum+p.arity+1 := by
  have he:=((selected_perm q p r hk hs).map
    (fun (a : At (Γ++Y++X++Θ) C)=>(G.exchangeR Δ Γ X Y Θ t).rho .right a)).sum_nat
  rw [List.map_map] at he
  let R : At K C→Nat := (q.performR Δ (G.exchangeR Δ Γ X Y Θ t)).rho .right
  have hh:=q.performR_rank Δ (G.exchangeR Δ Γ X Y Θ t)
  change R q.keep=(q.selected.map (fun (a : At (Γ++Y++X++Θ) C)=>(G.exchangeR Δ Γ X Y Θ t).rho .right a)).sum+_ at hh
  change R q.keep=_
  rw [ite_eq_left hn,←he] at hh
  simp only [Function.comp_def,G.rho_exchangeR_embedded] at hh
  let rt : At (Γ++X++Y++Θ) C→Nat := t.rho .right
  change R q.keep=(p.selected.map (fun a=>1+rt a)).sum+1 at hh
  change R q.keep=(p.selected.map rt).sum+p.arity+1
  rw [G.sum_map_one_add,p.selected_length] at hh
  omega
end DosenPetric.Reduced.Gentzen.UnrestrictedExchange
