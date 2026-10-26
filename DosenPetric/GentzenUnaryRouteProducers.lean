module

public import DosenPetric.GentzenUnaryRouteRepairBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.UnaryRouteReducer
universe u
variable {P : Type u} {C : NormalForm P} {F U K Δ Φ Ξ Ω Ψ : List (NormalForm P)}

theorem left_of_route (q : ContractionSelection C U K) (hn : 2≤q.arity)
    (w : G P U Δ) (t : G P F Δ) (j : Premise w t) (r : Route U F)
    (hb : w.branches=[⟨F,Δ,t,j⟩])
    (hp : ∀ {A : NormalForm P} (a : At F A),j.parent .left a=some (r.get a))
    (hw : ofTerm w.denote=comp (ofTerm r.product) (ofTerm t.denote))
    (hc : w.cutCount=t.cutCount)
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Ψ) :
    ReducesL cutLeft root (q.performL Δ w) q.keep := by
  obtain ⟨L,p,s,hs,hf⟩:=q.factor_route r (q.unary_preimageL hn w t j r hb hp)
  have hden:=repair_denoteL q p s r hs w t hw
  intro a hr
  refine ⟨repairL q p s t,?_,hden,?_⟩
  · change (repairL q p s t).cutCount=0
    rw [repair_countL]
    have h:=hr.cutFree
    change (q.performL Δ w).cutCount=0 at h
    rwa [q.performL_count,hc] at h
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩:=(a.replacement_cluster_iff _ b .left (.here C Ω) y).mp hv.2.1.1
    have hz' : z=q.keep:=hr.entry_unique z ha
    cases hz'
    exact (repair_boundL q r p s hf w t hn
      (fun x=>G.unary_route_rankL w t j r hb hp x)).bound b q.keep rfl y hz hv.2.1.2 hv.2.2.1

theorem right_of_route (q : ContractionSelection C U K) (hn : 2≤q.arity)
    (w : G P Δ U) (t : G P Δ F) (j : Premise w t) (r : Route U F)
    (hb : w.branches=[⟨Δ,F,t,j⟩])
    (hp : ∀ {A : NormalForm P} (a : At F A),j.parent .right a=some (r.get a))
    (hw : ofTerm w.denote=comp (ofTerm t.denote) (ofTerm r.coproduct))
    (hc : w.cutCount=t.cutCount)
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    ReducesR root cutRight (q.performR Δ w) q.keep := by
  obtain ⟨L,p,s,hs,hf⟩:=q.factor_route r (q.unary_preimageR hn w t j r hb hp)
  have hden:=repair_denoteR q p s r hs w t hw
  intro a hr
  refine ⟨repairR q p s t,?_,hden,?_⟩
  · change (repairR q p s t).cutCount=0
    rw [repair_countR]
    have h:=hr.cutFree
    change (q.performR Δ w).cutCount=0 at h
    rwa [q.performR_count,hc] at h
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩:=(a.replacement_cluster_iff _ b .right (.here C Ξ) y).mp hv.2.1.1
    have hz' : z=q.keep:=hr.entry_unique z ha
    cases hz'
    exact (repair_boundR q r p s hf w t hn
      (fun x=>G.unary_route_rankR w t j r hb hp x)).bound b q.keep rfl y hz hv.2.1.2 hv.2.2.1
end DosenPetric.Reduced.Gentzen.UnaryRouteReducer
