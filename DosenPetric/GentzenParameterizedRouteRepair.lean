module

public import DosenPetric.GentzenUnaryRouteRepairBounds
public import DosenPetric.GentzenInputRouteSupport

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.UnaryRouteReducer
universe u
variable {P : Type u} {C : NormalForm P} {F U K L Δ : List (NormalForm P)}
variable (q : ContractionSelection C U K) (r : Route U F)
variable (p : ContractionSelection C F L) (s : Route q.mask.erased p.mask.erased)
variable (tprog : StructuralProgram P q.mask.erased p.mask.erased)
variable (hf : (TraceRoute.full (r.map q.route.get)).fiber q.keep=p.selected)

def repairWithL (t : G P F Δ) : G P K Δ :=
  q.normalize.inverse.left ((tprog.consFixed C).left (p.normalize.left (p.performL Δ t)))
def repairWithR (t : G P Δ F) : G P Δ K :=
  q.normalize.inverse.right ((tprog.consFixed C).right (p.normalize.right (p.performR Δ t)))

theorem repairWith_countL (t : G P F Δ) :
    (repairWithL q p tprog t).cutCount=t.cutCount := by
  rw [repairWithL,ExchangeScript.left_count,StructuralProgram.left_count,
    ExchangeScript.left_count,ContractionSelection.performL_count]
theorem repairWith_countR (t : G P Δ F) :
    (repairWithR q p tprog t).cutCount=t.cutCount := by
  rw [repairWithR,ExchangeScript.right_count,StructuralProgram.right_count,
    ExchangeScript.right_count,ContractionSelection.performR_count]

theorem repairWith_atomizedL (t : G P F Δ) (hp : tprog.Atomic) (ht : t.Atomized) :
    (repairWithL q p tprog t).Atomized := by
  apply (q.normalize.inverse.left_atomized _).mpr
  apply StructuralProgram.left_atomized _ (tprog.atomic_consFixed C hp)
  exact (p.normalize.left_atomized _).mpr ((p.performL_atomized Δ t).mpr ht)
theorem repairWith_atomizedR (t : G P Δ F) (hp : tprog.Atomic) (ht : t.Atomized) :
    (repairWithR q p tprog t).Atomized := by
  apply (q.normalize.inverse.right_atomized _).mpr
  apply StructuralProgram.right_atomized _ (tprog.atomic_consFixed C hp)
  exact (p.normalize.right_atomized _).mpr ((p.performR_atomized Δ t).mpr ht)

theorem consFixed_arrow_eq (ht : ∀ {A : NormalForm P} (a : At p.mask.erased A),
    tprog.get a=s.get a) (o : Op) :
    (tprog.consFixed C).arrow o=(s.program.consFixed C).arrow o := by
  apply side_ext o
  intro A a
  rw [StructuralProgram.component,StructuralProgram.component]
  cases a with
  | here => rw [StructuralProgram.consFixed_here,StructuralProgram.consFixed_here]
  | there a => rw [StructuralProgram.consFixed_there,StructuralProgram.consFixed_there,ht,Route.program_get]

theorem repairWith_denoteL
    (hs : ∀ {A : NormalForm P} (a : At F A),
      q.route.get (r.get a)=q.normalize.inverse.get
        ((s.program.consFixed C).get (p.normalize.get (p.route.get a))))
    (ht : ∀ {A : NormalForm P} (a : At p.mask.erased A), tprog.get a=s.get a)
    (w : G P U Δ) (t : G P F Δ)
    (hw : ofTerm w.denote=comp (ofTerm r.product) (ofTerm t.denote)) :
    ofTerm (repairWithL q p tprog t).denote=ofTerm (q.performL Δ w).denote := by
  have he := repair_denoteL q p s r hs w t hw
  rw [repairL,ExchangeScript.left_denote,StructuralProgram.left_denote] at he
  rw [repairWithL,ExchangeScript.left_denote,StructuralProgram.left_denote,
    consFixed_arrow_eq q p s tprog ht .conj]
  exact he

theorem repairWith_denoteR
    (hs : ∀ {A : NormalForm P} (a : At F A),
      q.route.get (r.get a)=q.normalize.inverse.get
        ((s.program.consFixed C).get (p.normalize.get (p.route.get a))))
    (ht : ∀ {A : NormalForm P} (a : At p.mask.erased A), tprog.get a=s.get a)
    (w : G P Δ U) (t : G P Δ F)
    (hw : ofTerm w.denote=comp (ofTerm t.denote) (ofTerm r.coproduct)) :
    ofTerm (repairWithR q p tprog t).denote=ofTerm (q.performR Δ w).denote := by
  have he := repair_denoteR q p s r hs w t hw
  rw [repairR,ExchangeScript.right_denote,StructuralProgram.right_denote] at he
  rw [repairWithR,ExchangeScript.right_denote,StructuralProgram.right_denote,
    consFixed_arrow_eq q p s tprog ht .disj]
  exact he

include hf

theorem repairWith_boundL (w : G P U Δ) (t : G P F Δ) (hn : 2≤q.arity)
    (hr : ∀ x : At U C,w.rho .left x=1+(((TraceRoute.full r).fiber x).map
      (fun (a : At F C)=>t.rho .left a)).sum) :
    ContractionBound .left C ((q.performL Δ w).rho .left q.keep)
      (repairWithL q p tprog t) (fun a=>a=q.keep) := by
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
  have h2:=StructuralProgram.consFixed_boundL tprog (p.normalize.left (p.performL Δ t)) h1
  apply q.normalize.inverse.bound_left
  apply h2.mono
  intro a ha
  have he:=congrArg q.normalize.get ha
  have he' : a=.here C q.mask.erased:=
    (q.normalize.get_inverse a).symm.trans (he.trans q.normalize_keep)
  exact congrArg At.index he'

theorem repairWith_boundR (w : G P Δ U) (t : G P Δ F) (hn : 2≤q.arity)
    (hr : ∀ x : At U C,w.rho .right x=1+(((TraceRoute.full r).fiber x).map
      (fun (a : At F C)=>t.rho .right a)).sum) :
    ContractionBound .right C ((q.performR Δ w).rho .right q.keep)
      (repairWithR q p tprog t) (fun a=>a=q.keep) := by
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
  have h2:=StructuralProgram.consFixed_boundR tprog (p.normalize.right (p.performR Δ t)) h1
  apply q.normalize.inverse.bound_right
  apply h2.mono
  intro a ha
  have he:=congrArg q.normalize.get ha
  have he' : a=.here C q.mask.erased:=
    (q.normalize.get_inverse a).symm.trans (he.trans q.normalize_keep)
  exact congrArg At.index he'
end DosenPetric.Reduced.Gentzen.UnaryRouteReducer
