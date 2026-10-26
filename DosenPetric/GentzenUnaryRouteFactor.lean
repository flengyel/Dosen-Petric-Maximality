module

public import DosenPetric.GentzenUnaryRouteFibers

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {C : NormalForm P}
namespace ContractionSelection
variable {F U K : List (NormalForm P)}

theorem factor_route (q : ContractionSelection C U K) (r : Route U F)
    (hn : ∃ a : At F C,q.route.get (r.get a)=q.keep) :
    ∃ (L : List (NormalForm P)) (p : ContractionSelection C F L)
      (s : Route q.mask.erased p.mask.erased),
      (∀ {A : NormalForm P} (a : At F A),
        q.route.get (r.get a)=q.normalize.inverse.get
          ((s.program.consFixed C).get (p.normalize.get (p.route.get a)))) ∧
      (TraceRoute.full (r.map q.route.get)).fiber q.keep=p.selected := by
  let R:=r.map q.route.get
  let T:=R.map q.normalize.get
  have ht : ∃ a : At F C,T.get a=.here C q.mask.erased := by
    obtain ⟨a,ha⟩:=hn
    refine ⟨a,?_⟩
    simp only [T,R,Route.get_map,ha,q.normalize_keep]
  obtain ⟨L,p,s,he,hm⟩:=T.anchored_factor ht
  have he' {A : NormalForm P} (a : At F A) :
      q.normalize.get (q.route.get (r.get a))=
        (s.program.consFixed C).get (p.normalize.get (p.route.get a)) := by
    have h:=congrArg (fun v : Route (C::q.mask.erased) F=>v.get a) he
    simpa only [T,R,Route.get_map] using h
  refine ⟨L,p,s,?_,?_⟩
  · intro A a
    exact (q.normalize.inverse_get (q.route.get (r.get a))).symm.trans
      (congrArg q.normalize.inverse.get (he' a))
  · apply At.ordered_ext _ _ (TraceRoute.fiber_ordered _ _) p.selected_ordered
    intro a
    rw [TraceRoute.fiber_correct,TraceRoute.get_full,Option.some.injEq,Route.get_map,hm]
    constructor
    · intro h
      simp only [T,R,Route.get_map]
      rw [h,q.normalize_keep]
    · intro h
      apply q.normalize.injective
      simp only [T,R,Route.get_map] at h
      exact h.trans q.normalize_keep.symm

end ContractionSelection
end DosenPetric.Reduced.Gentzen
