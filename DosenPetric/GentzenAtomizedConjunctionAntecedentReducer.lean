module

public import DosenPetric.GentzenAtomizedOppositeInputReducers
public import DosenPetric.GentzenAtomizedOppositeLeaves
public import DosenPetric.GentzenAtomizedMix

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ConjunctionReducer
universe u
variable {P : Type u} {A B C : NormalForm P} {F U K Δ Λ Φ Ξ Ω Ψ : List (NormalForm P)}

theorem selection_left_atomized (s : ContractionSelection C (F++U) K) (hn : 2≤s.arity)
    (f : G P F (A::Δ)) (g : G P U (B::Λ))
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Ψ) :
    AtomizedReducesL cutLeft root (s.performL _ (G.conjR f g)) s.keep := by
  obtain ⟨h⟩:=ContractionSelection.split_exists F U s
  cases h with
  | left p =>
    have hp : 2≤p.arity := by rwa [p.extend_arity] at hn
    change AtomizedReducesL cutLeft root (W5.OneConjunctionAntecedent.oldFirst p f g) (p.extend U).keep
    rw [p.extend_keep]
    exact W5.OneConjunctionAntecedent.reducesFirst_atomized p f g hp cutLeft root
  | right q =>
    have hq : 2≤q.arity := by rwa [q.prepend_arity] at hn
    change AtomizedReducesL cutLeft root (W5.OneConjunctionAntecedent.oldSecond q f g) (q.prependFixed F).keep
    rw [q.prepend_keep]
    exact W5.OneConjunctionAntecedent.reducesSecond_atomized q f g hq cutLeft root
  | both p q => exact W5.ConjunctionAntecedent.reduces_atomized p q f g cutLeft root

/-- Every actual left contraction over native conjunction-right. No positional
selection or context-equality hypothesis is supplied by the caller. -/
theorem left_atomized (d : ContractionBlock P (F++U) K) (hn : 2≤d.gs.length)
    (f : G P F (A::Δ)) (g : G P U (B::Λ))
    (cutLeft : G P Φ (d.C::Ξ)) (root : G P (d.C::Ω) Ψ) :
    AtomizedReducesL cutLeft root (d.applyL hn _ (G.conjR f g)) d.keep := by
  let p:=d.selection (d.nonempty hn)
  have hb : p.block=d := d.selection_block _
  have hp : 2≤p.arity := by
    have hc:=p.count
    have hg : p.gs.length=d.gs.length := congrArg (fun b => b.gs.length) hb
    omega
  have hSel:=selection_left_atomized p hp f g cutLeft root
  have hw : p.performL _ (G.conjR f g)=d.applyL hn _ (G.conjR f g) :=
    (p.performL_eq_apply hp _).trans (ContractionBlock.applyL_congr hb _ _ _ _)
  have hx : p.keep=d.keep := d.selection_keep hn
  rw [hw,hx] at hSel
  exact hSel
end DosenPetric.Reduced.Gentzen.ConjunctionReducer
