module

public import DosenPetric.GentzenAtomizedConjunctionAntecedentReducer
public import DosenPetric.GentzenAtomizedOppositeLeaves
public import DosenPetric.GentzenAtomizedMix

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ConjunctionReducer
variable {A B C : NormalForm P} {F U K Γ Θ Φ Ξ Ω Λ : List (NormalForm P)}

theorem selection_right_atomized (s : ContractionSelection C (.conj A B::(F++U)) K) (hn : 2≤s.arity)
    (f : G P Γ (A::F)) (g : G P Θ (B::U))
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Λ) :
    AtomizedReducesR root cutRight (s.performR (Γ++Θ) (G.conjR f g)) s.keep := by
  obtain ⟨h⟩:=ContractionSelection.head_split_exists F U s
  cases h with
  | onlyFresh => change 2≤1 at hn; omega
  | parametricLeft D p =>
    have hp : 2≤p.arity := by change 2≤(p.extend U).arity at hn; rwa [p.extend_arity] at hn
    change AtomizedReducesR root cutRight (W5.OneConjunction.oldFirst p f g) (.there (p.extend U).keep)
    rw [p.extend_keep]
    exact W5.OneConjunction.reducesFirst_atomized p hp f g root cutRight
  | parametricRight D q =>
    have hq : 2≤q.arity := by change 2≤(q.prependFixed F).arity at hn; rwa [q.prepend_arity] at hn
    change AtomizedReducesR root cutRight (W5.OneConjunction.oldSecond q f g) (.there (q.prependFixed F).keep)
    rw [q.prepend_keep]
    exact W5.OneConjunction.reducesSecond_atomized q hq f g root cutRight
  | parametricBoth D p q => exact W5.ParametricConjunction.reduces_atomized p q f g root cutRight
  | selectedLeft p =>
    change AtomizedReducesR root cutRight (W6.OneHeadConjunction.oldFirst p f g) (p.extend U).keep
    rw [p.extend_keep]
    exact W6.OneHeadConjunction.reducesFirst_atomized p f g root cutRight
  | selectedRight q =>
    change AtomizedReducesR root cutRight (W6.OneHeadConjunction.oldSecond q f g) (q.prependFixed F).keep
    rw [q.prepend_keep]
    exact W6.OneHeadConjunction.reducesSecond_atomized q f g root cutRight
  | selectedBoth p q => exact W6.HeadRight.reduces_atomized p q f g root cutRight

/-- Every actual right contraction over native conjunction-right. The six
nontrivial selection regimes and all matching data are obtained internally. -/
theorem right_atomized (d : ContractionBlock P (.conj A B::(F++U)) K) (hn : 2≤d.gs.length)
    (f : G P Γ (A::F)) (g : G P Θ (B::U))
    (root : G P Φ (d.C::Ξ)) (cutRight : G P (d.C::Ω) Λ) :
    AtomizedReducesR root cutRight (d.applyR hn _ (G.conjR f g)) d.keep := by
  let p:=d.selection (d.nonempty hn)
  have hb : p.block=d := d.selection_block _
  have hp : 2≤p.arity := by
    have hc:=p.count
    have hg : p.gs.length=d.gs.length := congrArg (fun b => b.gs.length) hb
    omega
  have hSel:=selection_right_atomized p hp f g root cutRight
  have hw : p.performR (Γ++Θ) (G.conjR f g)=d.applyR hn _ (G.conjR f g) :=
    (p.performR_eq_apply hp _).trans (ContractionBlock.applyR_congr hb _ _ _ _)
  have hx : p.keep=d.keep := d.selection_keep hn
  rw [hw,hx] at hSel
  exact hSel
end ConjunctionReducer
end DosenPetric.Reduced.Gentzen
