module

public import DosenPetric.GentzenExchangeReductionBounds
public import DosenPetric.GentzenReductionStatements
public import DosenPetric.GentzenConjunctionInputReducer

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.UnrestrictedExchange
universe u
variable {P : Type u} {C : NormalForm P} {Γ X Y Θ K Δ Φ Ξ Ω Ψ : List (NormalForm P)}

theorem selection_left (q : ContractionSelection C (Γ++Y++X++Θ) K) (hn : 2≤q.arity)
    (t : G P (Γ++X++Y++Θ) Δ)
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Ψ) :
    ReducesL cutLeft root (q.performL Δ (G.exchangeL Γ X Y Θ Δ t)) q.keep := by
  obtain ⟨K0,p,r,he,hk,hs⟩:=factor q
  intro a hr
  have hd:=denoteL q p r hs t
  refine ⟨r.left (p.performL Δ t),?_,hd,?_⟩
  · change (r.left (p.performL Δ t)).cutCount=0
    rw [r.left_count,p.performL_count]
    have hc:=hr.cutFree
    change (q.performL Δ (G.exchangeL Γ X Y Θ Δ t)).cutCount=0 at hc
    rwa [q.performL_count] at hc
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩:=
      (a.replacement_cluster_iff _ b .left (.here C Ω) y).mp hv.2.1.1
    have hx : z=q.keep:=hr.entry_unique z ha
    cases hx
    exact (boundL q p r hn he hk hs t).bound b q.keep rfl y hz hv.2.1.2 hv.2.2.1

theorem selection_right (q : ContractionSelection C (Γ++Y++X++Θ) K) (hn : 2≤q.arity)
    (t : G P Δ (Γ++X++Y++Θ))
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    ReducesR root cutRight (q.performR Δ (G.exchangeR Δ Γ X Y Θ t)) q.keep := by
  obtain ⟨K0,p,r,he,hk,hs⟩:=factor q
  intro a hr
  have hd:=denoteR q p r hs t
  refine ⟨r.right (p.performR Δ t),?_,hd,?_⟩
  · change (r.right (p.performR Δ t)).cutCount=0
    rw [r.right_count,p.performR_count]
    have hc:=hr.cutFree
    change (q.performR Δ (G.exchangeR Δ Γ X Y Θ t)).cutCount=0 at hc
    rwa [q.performR_count] at hc
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩:=
      (a.replacement_cluster_iff _ b .right (.here C Ξ) y).mp hv.2.1.1
    have hx : z=q.keep:=hr.entry_unique z ha
    cases hx
    exact (boundR q p r hn he hk hs t).bound b q.keep rfl y hz hv.2.1.2 hv.2.2.1

/-- Arbitrary actual same-side exchange below an actual left contraction.
The decomposition and all exit exchanges are constructed internally. -/
theorem left (d : ContractionBlock P (Γ++Y++X++Θ) K) (hn : 2≤d.gs.length)
    (t : G P (Γ++X++Y++Θ) Δ)
    (cutLeft : G P Φ (d.C::Ξ)) (root : G P (d.C::Ω) Ψ) :
    ReducesL cutLeft root (d.applyL hn Δ (G.exchangeL Γ X Y Θ Δ t)) d.keep := by
  let p:=d.selection (d.nonempty hn)
  have he : p.block=d:=d.selection_block _
  have hp : 2≤p.arity := by
    have h:=congrArg (fun b=>b.gs.length) he
    change p.gs.length=d.gs.length at h
    have hc:=p.count
    omega
  have h:=selection_left p hp t cutLeft root
  have hw : p.performL _ (G.exchangeL Γ X Y Θ Δ t)=d.applyL hn _ (G.exchangeL Γ X Y Θ Δ t) :=
    (p.performL_eq_apply hp _).trans (ContractionBlock.applyL_congr he _ _ _ _)
  have hx : p.keep=d.keep:=d.selection_keep hn
  rw [hw,hx] at h
  exact h

/-- Independently typed right-hand reducer, with no interval exclusion. -/
theorem right (d : ContractionBlock P (Γ++Y++X++Θ) K) (hn : 2≤d.gs.length)
    (t : G P Δ (Γ++X++Y++Θ))
    (root : G P Φ (d.C::Ξ)) (cutRight : G P (d.C::Ω) Ψ) :
    ReducesR root cutRight (d.applyR hn Δ (G.exchangeR Δ Γ X Y Θ t)) d.keep := by
  let p:=d.selection (d.nonempty hn)
  have he : p.block=d:=d.selection_block _
  have hp : 2≤p.arity := by
    have h:=congrArg (fun b=>b.gs.length) he
    change p.gs.length=d.gs.length at h
    have hc:=p.count
    omega
  have h:=selection_right p hp t root cutRight
  have hw : p.performR _ (G.exchangeR Δ Γ X Y Θ t)=d.applyR hn _ (G.exchangeR Δ Γ X Y Θ t) :=
    (p.performR_eq_apply hp _).trans (ContractionBlock.applyR_congr he _ _ _ _)
  have hx : p.keep=d.keep:=d.selection_keep hn
  rw [hw,hx] at h
  exact h
end DosenPetric.Reduced.Gentzen.UnrestrictedExchange
