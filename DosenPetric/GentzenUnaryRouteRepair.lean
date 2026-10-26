module

public import DosenPetric.GentzenUnaryRouteFactorLaws

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.UnaryRouteReducer
universe u
variable {P : Type u} {C : NormalForm P} {F U K L Δ : List (NormalForm P)}
variable (q : ContractionSelection C U K) (p : ContractionSelection C F L)
variable (s : Route q.mask.erased p.mask.erased)

def repairL (t : G P F Δ) : G P K Δ :=
  q.normalize.inverse.left ((s.program.consFixed C).left (p.normalize.left (p.performL Δ t)))
def repairR (t : G P Δ F) : G P Δ K :=
  q.normalize.inverse.right ((s.program.consFixed C).right (p.normalize.right (p.performR Δ t)))

theorem repair_countL (t : G P F Δ) : (repairL q p s t).cutCount=t.cutCount := by
  rw [repairL,ExchangeScript.left_count,StructuralProgram.left_count,ExchangeScript.left_count,
    ContractionSelection.performL_count]

theorem repair_countR (t : G P Δ F) : (repairR q p s t).cutCount=t.cutCount := by
  rw [repairR,ExchangeScript.right_count,StructuralProgram.right_count,ExchangeScript.right_count,
    ContractionSelection.performR_count]

variable (r : Route U F)
variable (hs : ∀ {A : NormalForm P} (a : At F A),
  q.route.get (r.get a)=q.normalize.inverse.get
    ((s.program.consFixed C).get (p.normalize.get (p.route.get a))))

include hs in
theorem repair_denoteL (w : G P U Δ) (t : G P F Δ)
    (hw : ofTerm w.denote=comp (ofTerm r.product) (ofTerm t.denote)) :
    ofTerm (repairL q p s t).denote=ofTerm (q.performL Δ w).denote := by
  rw [repairL,ExchangeScript.left_denote,StructuralProgram.left_denote,ExchangeScript.left_denote,
    ContractionSelection.performL_denote,ContractionSelection.performL_denote,hw]
  let d : (side P .conj).Hom (fold .conj F) (succ Δ):=ofTerm t.denote
  change (side P .conj).comp (q.normalize.inverse.arrow .conj)
    ((side P .conj).comp ((s.program.consFixed C).arrow .conj)
      ((side P .conj).comp (p.normalize.arrow .conj)
        ((side P .conj).comp (p.route.sideArrow .conj) d)))=
    (side P .conj).comp (q.route.sideArrow .conj) ((side P .conj).comp (r.sideArrow .conj) d)
  symm
  simpa only [(side P .conj).assoc] using
    congrArg (fun k=>(side P .conj).comp k d) (factor_side q r p s hs .conj)

include hs in
theorem repair_denoteR (w : G P Δ U) (t : G P Δ F)
    (hw : ofTerm w.denote=comp (ofTerm t.denote) (ofTerm r.coproduct)) :
    ofTerm (repairR q p s t).denote=ofTerm (q.performR Δ w).denote := by
  rw [repairR,ExchangeScript.right_denote,StructuralProgram.right_denote,ExchangeScript.right_denote,
    ContractionSelection.performR_denote,ContractionSelection.performR_denote,hw]
  let d : (side P .disj).Hom (fold .disj F) (ante Δ):=ofTerm t.denote
  change (side P .disj).comp (q.normalize.inverse.arrow .disj)
    ((side P .disj).comp ((s.program.consFixed C).arrow .disj)
      ((side P .disj).comp (p.normalize.arrow .disj)
        ((side P .disj).comp (p.route.sideArrow .disj) d)))=
    (side P .disj).comp (q.route.sideArrow .disj) ((side P .disj).comp (r.sideArrow .disj) d)
  symm
  simpa only [(side P .disj).assoc] using
    congrArg (fun k=>(side P .disj).comp k d) (factor_side q r p s hs .disj)
end DosenPetric.Reduced.Gentzen.UnaryRouteReducer
