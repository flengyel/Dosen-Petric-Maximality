module

public import DosenPetric.GentzenOneHeadDisjunctionBounds
public import DosenPetric.GentzenReducibilityNativeLogical

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace W6.NativeLeft
theorem reduces {A B : NormalForm P} {F K U L Δ Λ Φ Ξ Ω Ψ : List (NormalForm P)}
    (p : ContractionSelection (.disj A B) F K) (q : ContractionSelection (.disj A B) U L)
    (f : G P (A::F) Δ) (g : G P (B::U) Λ)
    (cutLeft : G P Φ (.disj A B::Ξ)) (root : G P (.disj A B::Ω) Ψ) :
    ReducesL cutLeft root (old p q f g) (p.chain q).keep := by
  intro a hr
  have h:=addressed_left p q f g a hr
  exact ⟨repair p q f g,h.1,h.2.1,h.2.2.2⟩
end W6.NativeLeft
namespace DisjunctionReducer
variable {A B C : NormalForm P} {F U K Δ Λ Φ Ξ Ω Ψ : List (NormalForm P)}

theorem selection_left (s : ContractionSelection C (.disj A B::(F++U)) K) (hn : 2≤s.arity)
    (f : G P (A::F) Δ) (g : G P (B::U) Λ)
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Ψ) :
    ReducesL cutLeft root (s.performL (Δ++Λ) (G.disjL f g)) s.keep := by
  obtain ⟨h⟩:=ContractionSelection.head_split_exists F U s
  cases h with
  | onlyFresh => change 2≤1 at hn; omega
  | parametricLeft D p =>
    have hp : 2≤p.arity := by change 2≤(p.extend U).arity at hn; rwa [p.extend_arity] at hn
    change ReducesL cutLeft root (W5.OneDisjunctionAntecedent.oldFirst p f g) (.there (p.extend U).keep)
    rw [p.extend_keep]
    exact W5.OneDisjunctionAntecedent.reducesFirst p hp f g cutLeft root
  | parametricRight D q =>
    have hq : 2≤q.arity := by change 2≤(q.prependFixed F).arity at hn; rwa [q.prepend_arity] at hn
    change ReducesL cutLeft root (W5.OneDisjunctionAntecedent.oldSecond q f g) (.there (q.prependFixed F).keep)
    rw [q.prepend_keep]
    exact W5.OneDisjunctionAntecedent.reducesSecond q hq f g cutLeft root
  | parametricBoth D p q => exact W5.ParametricDisjunction.reduces p q f g cutLeft root
  | selectedLeft p =>
    change ReducesL cutLeft root (W6.OneHeadDisjunction.oldFirst p f g) (p.extend U).keep
    rw [p.extend_keep]
    exact W6.OneHeadDisjunction.reducesFirst p f g cutLeft root
  | selectedRight q =>
    change ReducesL cutLeft root (W6.OneHeadDisjunction.oldSecond q f g) (q.prependFixed F).keep
    rw [q.prepend_keep]
    exact W6.OneHeadDisjunction.reducesSecond q f g cutLeft root
  | selectedBoth p q => exact W6.NativeLeft.reduces p q f g cutLeft root

/-- Every actual left contraction over native disjunction-left. The six
nontrivial selection regimes and all matching data are obtained internally. -/
theorem left (d : ContractionBlock P (.disj A B::(F++U)) K) (hn : 2≤d.gs.length)
    (f : G P (A::F) Δ) (g : G P (B::U) Λ)
    (cutLeft : G P Φ (d.C::Ξ)) (root : G P (d.C::Ω) Ψ) :
    ReducesL cutLeft root (d.applyL hn _ (G.disjL f g)) d.keep := by
  let p:=d.selection (d.nonempty hn)
  have hb : p.block=d := d.selection_block _
  have hp : 2≤p.arity := by
    have hc:=p.count
    have hg : p.gs.length=d.gs.length := congrArg (fun b => b.gs.length) hb
    omega
  have hSel:=selection_left p hp f g cutLeft root
  have hw : p.performL (Δ++Λ) (G.disjL f g)=d.applyL hn _ (G.disjL f g) :=
    (p.performL_eq_apply hp _).trans (ContractionBlock.applyL_congr hb _ _ _ _)
  have hx : p.keep=d.keep := d.selection_keep hn
  rw [hw,hx] at hSel
  exact hSel
end DisjunctionReducer
end DosenPetric.Reduced.Gentzen
