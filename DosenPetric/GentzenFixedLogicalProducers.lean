module

public import DosenPetric.GentzenFixedLogicalRepairBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.FixedLogicalReducer
universe u
variable {P : Type u} {C A B : NormalForm P} {Γ Θ K Δ Φ Ξ Ω Ψ : List (NormalForm P)}
variable (g : SelectionMask C Γ) (t : SelectionMask C Θ)

theorem left (q : ContractionSelection C (Γ++.conj A B::Θ) K) (hn : 2≤q.arity)
    (hq : q.mask=SelectionMask.contextMask g t [.conj A B])
    (f : G P (Γ++A::B::Θ) Δ) (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Ψ) :
    ReducesL cutLeft root (q.performL Δ (G.conjL Γ Θ Δ A B f)) q.keep := by
  have hm : 0<(SelectionMask.contextMask g t [A,B]).count := by
    rw [SelectionMask.context_count]
    have he:=q.context_arity g t [.conj A B] hq
    omega
  obtain ⟨L,p,hp⟩:=(SelectionMask.contextMask g t [A,B]).selection_exists hm
  intro a hr
  have he:=denoteL g t q p hq hp f
  refine ⟨repairL g t q p hq hp f,?_,he,?_⟩
  · change (repairL g t q p hq hp f).cutCount=0
    rw [repair_countL]
    have hc:=hr.cutFree
    change (q.performL Δ (G.conjL Γ Θ Δ A B f)).cutCount=0 at hc
    rwa [q.performL_count] at hc
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩:=(a.replacement_cluster_iff _ b .left (.here C Ω) y).mp hv.2.1.1
    have hx : z=q.keep:=hr.entry_unique z ha
    cases hx
    exact (repair_boundL g t q p hq hp f hn).bound b q.keep rfl y hz hv.2.1.2 hv.2.2.1

theorem right (q : ContractionSelection C (Γ++.disj A B::Θ) K) (hn : 2≤q.arity)
    (hq : q.mask=SelectionMask.contextMask g t [.disj A B])
    (f : G P Δ (Γ++A::B::Θ)) (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    ReducesR root cutRight (q.performR Δ (G.disjR Δ Γ Θ A B f)) q.keep := by
  have hm : 0<(SelectionMask.contextMask g t [A,B]).count := by
    rw [SelectionMask.context_count]
    have he:=q.context_arity g t [.disj A B] hq
    omega
  obtain ⟨L,p,hp⟩:=(SelectionMask.contextMask g t [A,B]).selection_exists hm
  intro a hr
  have he:=denoteR g t q p hq hp f
  refine ⟨repairR g t q p hq hp f,?_,he,?_⟩
  · change (repairR g t q p hq hp f).cutCount=0
    rw [repair_countR]
    have hc:=hr.cutFree
    change (q.performR Δ (G.disjR Δ Γ Θ A B f)).cutCount=0 at hc
    rwa [q.performR_count] at hc
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩:=(a.replacement_cluster_iff _ b .right (.here C Ξ) y).mp hv.2.1.1
    have hx : z=q.keep:=hr.entry_unique z ha
    cases hx
    exact (repair_boundR g t q p hq hp f hn).bound b q.keep rfl y hz hv.2.1.2 hv.2.2.1
end DosenPetric.Reduced.Gentzen.FixedLogicalReducer
