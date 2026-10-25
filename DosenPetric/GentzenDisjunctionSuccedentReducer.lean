module

public import DosenPetric.GentzenDisjunctionSuccedentOne

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.DisjunctionReducer
universe u
variable {P : Type u} {A B C : NormalForm P} {F U K Γ Θ Φ Ξ Ω Ψ : List (NormalForm P)}

theorem selection_right (s : ContractionSelection C (F++U) K) (hn : 2≤s.arity)
    (f : G P (A::Γ) F) (g : G P (B::Θ) U)
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    ReducesR root cutRight (s.performR _ (G.disjL f g)) s.keep := by
  obtain ⟨h⟩:=ContractionSelection.split_exists F U s
  cases h with
  | left p =>
    have hp : 2≤p.arity := by rwa [p.extend_arity] at hn
    change ReducesR root cutRight (W5.OneDisjunctionSuccedent.oldFirst p f g) (p.extend U).keep
    rw [p.extend_keep]
    exact W5.OneDisjunctionSuccedent.reducesFirst p f g hp root cutRight
  | right q =>
    have hq : 2≤q.arity := by rwa [q.prepend_arity] at hn
    change ReducesR root cutRight (W5.OneDisjunctionSuccedent.oldSecond q f g) (q.prependFixed F).keep
    rw [q.prepend_keep]
    exact W5.OneDisjunctionSuccedent.reducesSecond q f g hq root cutRight
  | both p q => exact W5.DisjunctionSuccedent.reduces p q f g root cutRight

/-- Every actual right contraction over native disjunction-left. No positional
selection or context-equality hypothesis is supplied by the caller. -/
theorem right (d : ContractionBlock P (F++U) K) (hn : 2≤d.gs.length)
    (f : G P (A::Γ) F) (g : G P (B::Θ) U)
    (root : G P Φ (d.C::Ξ)) (cutRight : G P (d.C::Ω) Ψ) :
    ReducesR root cutRight (d.applyR hn _ (G.disjL f g)) d.keep := by
  let p:=d.selection (d.nonempty hn)
  have hb : p.block=d := d.selection_block _
  have hp : 2≤p.arity := by
    have hc:=p.count
    have hg : p.gs.length=d.gs.length := congrArg (fun b => b.gs.length) hb
    omega
  have hSel:=selection_right p hp f g root cutRight
  have hw : p.performR _ (G.disjL f g)=d.applyR hn _ (G.disjL f g) :=
    (p.performR_eq_apply hp _).trans (ContractionBlock.applyR_congr hb _ _ _ _)
  have hx : p.keep=d.keep := d.selection_keep hn
  rw [hw,hx] at hSel
  exact hSel
end DosenPetric.Reduced.Gentzen.DisjunctionReducer
