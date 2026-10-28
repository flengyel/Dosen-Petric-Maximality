module

public import DosenPetric.GentzenAtomizedBinaryLeaves

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace DosenPetric.Reduced.Gentzen.FixedLogicalReducer
universe u
variable {P : Type u} {C A B : NormalForm P} {Γ Θ K Δ Φ Ξ Ω Ψ : List (NormalForm P)}
variable (g : SelectionMask C Γ) (t : SelectionMask C Θ)

theorem left_atomized (q : ContractionSelection C (Γ++.conj A B::Θ) K) (hn : 2≤q.arity)
    (hq : q.mask=SelectionMask.contextMask g t [.conj A B])
    (f : G P (Γ++A::B::Θ) Δ) (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Ψ) :
    AtomizedReducesL cutLeft root (q.performL Δ (G.conjL Γ Θ Δ A B f)) q.keep := by
  have hm : 0<(SelectionMask.contextMask g t [A,B]).count := by
    rw [SelectionMask.context_count]
    have he:=q.context_arity g t [.conj A B] hq
    omega
  obtain ⟨L,p,hp⟩:=(SelectionMask.contextMask g t [A,B]).selection_exists hm
  intro hat a hr
  have he:=denoteL g t q p hq hp f
  refine ⟨repairL g t q p hq hp f,?_,?_,he,?_⟩
  · change (repairL g t q p hq hp f).cutCount=0
    rw [repair_countL]
    have hc:=hr.cutFree
    change (q.performL Δ (G.conjL Γ Θ Δ A B f)).cutCount=0 at hc
    rwa [q.performL_count] at hc
  · simpa only [repairL,ExchangeScript.left_atomized,G.Atomized,ContractionSelection.performL_atomized] using hat
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩:=(a.replacement_cluster_iff _ b .left (.here C Ω) y).mp hv.2.1.1
    have hx : z=q.keep:=hr.entry_unique z ha
    cases hx
    exact (repair_boundL g t q p hq hp f hn).bound b q.keep rfl y hz hv.2.1.2 hv.2.2.1

theorem right_atomized (q : ContractionSelection C (Γ++.disj A B::Θ) K) (hn : 2≤q.arity)
    (hq : q.mask=SelectionMask.contextMask g t [.disj A B])
    (f : G P Δ (Γ++A::B::Θ)) (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    AtomizedReducesR root cutRight (q.performR Δ (G.disjR Δ Γ Θ A B f)) q.keep := by
  have hm : 0<(SelectionMask.contextMask g t [A,B]).count := by
    rw [SelectionMask.context_count]
    have he:=q.context_arity g t [.disj A B] hq
    omega
  obtain ⟨L,p,hp⟩:=(SelectionMask.contextMask g t [A,B]).selection_exists hm
  intro hat a hr
  have he:=denoteR g t q p hq hp f
  refine ⟨repairR g t q p hq hp f,?_,?_,he,?_⟩
  · change (repairR g t q p hq hp f).cutCount=0
    rw [repair_countR]
    have hc:=hr.cutFree
    change (q.performR Δ (G.disjR Δ Γ Θ A B f)).cutCount=0 at hc
    rwa [q.performR_count] at hc
  · simpa only [repairR,ExchangeScript.right_atomized,G.Atomized,ContractionSelection.performR_atomized] using hat
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩:=(a.replacement_cluster_iff _ b .right (.here C Ξ) y).mp hv.2.1.1
    have hx : z=q.keep:=hr.entry_unique z ha
    cases hx
    exact (repair_boundR g t q p hq hp f hn).bound b q.keep rfl y hz hv.2.1.2 hv.2.2.1
end DosenPetric.Reduced.Gentzen.FixedLogicalReducer

namespace DosenPetric.Reduced.Gentzen.SelectedLogicalReducer
universe u
variable {P : Type u} {A B : NormalForm P} {Γ Θ K Δ Φ Ξ Ω Ψ : List (NormalForm P)}

theorem left_atomized (g : SelectionMask (.conj A B) Γ) (t : SelectionMask (.conj A B) Θ)
    (q : ContractionSelection (.conj A B) (Γ++.conj A B::Θ) K) (hn : 2≤q.arity)
    (hq : q.mask=SelectionMask.selectedContext g t)
    (f : G P (Γ++A::B::Θ) Δ) (cutLeft : G P Φ (.conj A B::Ξ)) (root : G P (.conj A B::Ω) Ψ) :
    AtomizedReducesL cutLeft root (q.performL Δ (G.conjL Γ Θ Δ A B f)) q.keep := by
  have hm : 0<(g.append t).count := by
    have he:=q.mask_count
    rw [hq,SelectionMask.selectedContext_count] at he
    rw [SelectionMask.append_count]
    omega
  obtain ⟨L,p,hp⟩:=(g.append t).selection_exists hm
  intro hat a hr
  have he:=denoteL g t q p hq hp f
  refine ⟨repairL g t q p hq hp f,?_,?_,he,?_⟩
  · change (repairL g t q p hq hp f).cutCount=0
    rw [countL]
    have hc:=hr.cutFree
    change (q.performL Δ (G.conjL Γ Θ Δ A B f)).cutCount=0 at hc
    rwa [q.performL_count] at hc
  · simpa only [repairL,ExchangeScript.left_atomized,G.Atomized,ContractionSelection.performL_atomized,sourceRepairL,W4.NonemptyLeft.transported,G.atomized_reindex,W4.NonemptyLeft.atomized,G.moveEndL,UnaryCast.exchangeL] using hat
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩:=(a.replacement_cluster_iff _ b .left (.here (.conj A B) Ω) y).mp hv.2.1.1
    have hx : z=q.keep:=hr.entry_unique z ha
    cases hx
    exact (boundL g t q p hq hp f hn).bound b q.keep rfl y hz hv.2.1.2 hv.2.2.1

theorem right_atomized (g : SelectionMask (.disj A B) Γ) (t : SelectionMask (.disj A B) Θ)
    (q : ContractionSelection (.disj A B) (Γ++.disj A B::Θ) K) (hn : 2≤q.arity)
    (hq : q.mask=SelectionMask.selectedContext g t)
    (f : G P Δ (Γ++A::B::Θ)) (root : G P Φ (.disj A B::Ξ)) (cutRight : G P (.disj A B::Ω) Ψ) :
    AtomizedReducesR root cutRight (q.performR Δ (G.disjR Δ Γ Θ A B f)) q.keep := by
  have hm : 0<(g.append t).count := by
    have he:=q.mask_count
    rw [hq,SelectionMask.selectedContext_count] at he
    rw [SelectionMask.append_count]
    omega
  obtain ⟨L,p,hp⟩:=(g.append t).selection_exists hm
  intro hat a hr
  have he:=denoteR g t q p hq hp f
  refine ⟨repairR g t q p hq hp f,?_,?_,he,?_⟩
  · change (repairR g t q p hq hp f).cutCount=0
    rw [countR]
    have hc:=hr.cutFree
    change (q.performR Δ (G.disjR Δ Γ Θ A B f)).cutCount=0 at hc
    rwa [q.performR_count] at hc
  · simpa only [repairR,ExchangeScript.right_atomized,G.Atomized,ContractionSelection.performR_atomized,sourceRepairR,W4.NonemptyRight.transported,G.atomized_reindex,W4.NonemptyRight.atomized,G.moveEndR,UnaryCast.exchangeR] using hat
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩:=(a.replacement_cluster_iff _ b .right (.here (.disj A B) Ξ) y).mp hv.2.1.1
    have hx : z=q.keep:=hr.entry_unique z ha
    cases hx
    exact (boundR g t q p hq hp f hn).bound b q.keep rfl y hz hv.2.1.2 hv.2.2.1
end DosenPetric.Reduced.Gentzen.SelectedLogicalReducer
