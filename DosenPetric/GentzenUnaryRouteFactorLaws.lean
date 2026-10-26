module

public import DosenPetric.GentzenUnaryRouteFactor

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.UnaryRouteReducer
universe u
variable {P : Type u} {C : NormalForm P} {F U K L : List (NormalForm P)}
variable (q : ContractionSelection C U K) (r : Route U F)
variable (p : ContractionSelection C F L) (s : Route q.mask.erased p.mask.erased)
variable (hs : ∀ {A : NormalForm P} (a : At F A),
  q.route.get (r.get a)=q.normalize.inverse.get
    ((s.program.consFixed C).get (p.normalize.get (p.route.get a))))
variable (hf : (TraceRoute.full (r.map q.route.get)).fiber q.keep=p.selected)

include hs in
theorem factor_side (o : Op) :
    (side P o).comp (q.route.sideArrow o) (r.sideArrow o)=
      (side P o).comp (q.normalize.inverse.arrow o)
        ((side P o).comp ((s.program.consFixed C).arrow o)
          ((side P o).comp (p.normalize.arrow o) (p.route.sideArrow o))) := by
  apply side_ext o
  intro A a
  rw [(side P o).assoc,Route.sideArrow_get,Route.sideArrow_get,
    (side P o).assoc,(side P o).assoc,(side P o).assoc,
    Route.sideArrow_get,ExchangeScript.component,StructuralProgram.component,ExchangeScript.component,hs]

include hf in
theorem selected_sum (rho : At F C→Nat) :
    (p.selected.map rho).sum=
      (q.selected.map (fun x=>(((TraceRoute.full r).fiber x).map rho).sum)).sum := by
  have hq : (TraceRoute.full q.route).fiber q.keep=q.selected := by
    apply At.ordered_ext _ _ (TraceRoute.fiber_ordered _ _) q.selected_ordered
    intro a
    rw [TraceRoute.fiber_correct,TraceRoute.get_full,Option.some.injEq,←q.selected_iff]
  have h:=TraceRoute.sum_fiber_comp r q.route q.keep rho
  rw [hf,hq] at h
  exact h

include hf in
theorem old_rankL {Δ : List (NormalForm P)} (w : G P U Δ) (t : G P F Δ) (hn : 2≤q.arity)
    (hr : ∀ x : At U C,w.rho .left x=1+(((TraceRoute.full r).fiber x).map
      (fun (a : At F C)=>t.rho .left a)).sum) :
    (q.performL Δ w).rho .left q.keep=(p.selected.map (fun a=>t.rho .left a)).sum+q.arity+1 := by
  let R : At K C→Nat:=(q.performL Δ w).rho .left
  let rt : At F C→Nat:=t.rho .left
  let rw : At U C→Nat:=w.rho .left
  let b : At U C→Nat:=fun x=>(((TraceRoute.full r).fiber x).map rt).sum
  have hm : q.selected.map rw=q.selected.map (fun x=>1+b x) := by
    apply List.map_congr_left
    intro x _;exact hr x
  have hh:=q.performL_rank Δ w
  change R q.keep=(q.selected.map rw).sum+_ at hh
  rw [ite_eq_left hn,hm,G.sum_map_one_add,q.selected_length] at hh
  have hh':=(selected_sum q r p hf rt)
  change (p.selected.map rt).sum=(q.selected.map b).sum at hh'
  change R q.keep=(p.selected.map rt).sum+q.arity+1
  omega

include hf in
theorem old_rankR {Δ : List (NormalForm P)} (w : G P Δ U) (t : G P Δ F) (hn : 2≤q.arity)
    (hr : ∀ x : At U C,w.rho .right x=1+(((TraceRoute.full r).fiber x).map
      (fun (a : At F C)=>t.rho .right a)).sum) :
    (q.performR Δ w).rho .right q.keep=(p.selected.map (fun a=>t.rho .right a)).sum+q.arity+1 := by
  let R : At K C→Nat:=(q.performR Δ w).rho .right
  let rt : At F C→Nat:=t.rho .right
  let rw : At U C→Nat:=w.rho .right
  let b : At U C→Nat:=fun x=>(((TraceRoute.full r).fiber x).map rt).sum
  have hm : q.selected.map rw=q.selected.map (fun x=>1+b x) := by
    apply List.map_congr_left
    intro x _;exact hr x
  have hh:=q.performR_rank Δ w
  change R q.keep=(q.selected.map rw).sum+_ at hh
  rw [ite_eq_left hn,hm,G.sum_map_one_add,q.selected_length] at hh
  have hh':=(selected_sum q r p hf rt)
  change (p.selected.map rt).sum=(q.selected.map b).sum at hh'
  change R q.keep=(p.selected.map rt).sum+q.arity+1
  omega
end DosenPetric.Reduced.Gentzen.UnaryRouteReducer
