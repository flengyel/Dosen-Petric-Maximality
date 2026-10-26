module

public import DosenPetric.GentzenUnaryRouteRepair

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.UnaryRouteReducer
universe u
variable {P : Type u} {C : NormalForm P} {F U K L Δ : List (NormalForm P)}
variable (q : ContractionSelection C U K) (r : Route U F)
variable (p : ContractionSelection C F L) (s : Route q.mask.erased p.mask.erased)
variable (hf : (TraceRoute.full (r.map q.route.get)).fiber q.keep=p.selected)

include hf

theorem repair_boundL (w : G P U Δ) (t : G P F Δ) (hn : 2≤q.arity)
    (hr : ∀ x : At U C,w.rho .left x=1+(((TraceRoute.full r).fiber x).map
      (fun (a : At F C)=>t.rho .left a)).sum) :
    ContractionBound .left C ((q.performL Δ w).rho .left q.keep)
      (repairL q p s t) (fun a=>a=q.keep) := by
  have hb : (p.performL Δ t).rho .left p.keep < (q.performL Δ w).rho .left q.keep := by
    let R : At L C→Nat:=(p.performL Δ t).rho .left
    let O : At K C→Nat:=(q.performL Δ w).rho .left
    let rt : At F C→Nat:=t.rho .left
    have h0:=old_rankL q r p hf w t hn hr
    have h1:=p.performL_rank Δ t
    change O q.keep=(p.selected.map rt).sum+q.arity+1 at h0
    change R p.keep=(p.selected.map rt).sum+_ at h1
    change R p.keep<O q.keep
    split at h1 <;> omega
  have h0 : ContractionBound .left C ((q.performL Δ w).rho .left q.keep)
      (p.performL Δ t) (fun a=>a=p.keep) := by
    apply ContractionBound.bounded
    intro a ha
    cases ha
    exact hb
  have h1 : ContractionBound .left C ((q.performL Δ w).rho .left q.keep)
      (p.normalize.left (p.performL Δ t)) (fun a=>a.index=0) := by
    apply p.normalize.bound_left
    apply h0.mono
    intro a ha
    apply p.normalize.injective
    have he : p.normalize.get a=.here C p.mask.erased:=At.index_injective _ _ ha
    exact he.trans p.normalize_keep.symm
  have h2:=StructuralProgram.consFixed_boundL s.program (p.normalize.left (p.performL Δ t)) h1
  apply q.normalize.inverse.bound_left
  apply h2.mono
  intro a ha
  have he:=congrArg q.normalize.get ha
  have he' : a=.here C q.mask.erased:=
    (q.normalize.get_inverse a).symm.trans (he.trans q.normalize_keep)
  exact congrArg At.index he'

theorem repair_boundR (w : G P Δ U) (t : G P Δ F) (hn : 2≤q.arity)
    (hr : ∀ x : At U C,w.rho .right x=1+(((TraceRoute.full r).fiber x).map
      (fun (a : At F C)=>t.rho .right a)).sum) :
    ContractionBound .right C ((q.performR Δ w).rho .right q.keep)
      (repairR q p s t) (fun a=>a=q.keep) := by
  have hb : (p.performR Δ t).rho .right p.keep < (q.performR Δ w).rho .right q.keep := by
    let R : At L C→Nat:=(p.performR Δ t).rho .right
    let O : At K C→Nat:=(q.performR Δ w).rho .right
    let rt : At F C→Nat:=t.rho .right
    have h0:=old_rankR q r p hf w t hn hr
    have h1:=p.performR_rank Δ t
    change O q.keep=(p.selected.map rt).sum+q.arity+1 at h0
    change R p.keep=(p.selected.map rt).sum+_ at h1
    change R p.keep<O q.keep
    split at h1 <;> omega
  have h0 : ContractionBound .right C ((q.performR Δ w).rho .right q.keep)
      (p.performR Δ t) (fun a=>a=p.keep) := by
    apply ContractionBound.bounded
    intro a ha
    cases ha
    exact hb
  have h1 : ContractionBound .right C ((q.performR Δ w).rho .right q.keep)
      (p.normalize.right (p.performR Δ t)) (fun a=>a.index=0) := by
    apply p.normalize.bound_right
    apply h0.mono
    intro a ha
    apply p.normalize.injective
    have he : p.normalize.get a=.here C p.mask.erased:=At.index_injective _ _ ha
    exact he.trans p.normalize_keep.symm
  have h2:=StructuralProgram.consFixed_boundR s.program (p.normalize.right (p.performR Δ t)) h1
  apply q.normalize.inverse.bound_right
  apply h2.mono
  intro a ha
  have he:=congrArg q.normalize.get ha
  have he' : a=.here C q.mask.erased:=
    (q.normalize.get_inverse a).symm.trans (he.trans q.normalize_keep)
  exact congrArg At.index he'
end DosenPetric.Reduced.Gentzen.UnaryRouteReducer
