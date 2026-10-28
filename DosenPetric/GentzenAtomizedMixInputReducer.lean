module

public import DosenPetric.GentzenAtomizedDisjunctionSuccedentReducer
public import DosenPetric.GentzenAtomizedOppositeLeaves
public import DosenPetric.GentzenAtomizedMix

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.MixReducer
universe u
variable {P : Type u} {F U K Δ Λ Γ Ξ Θ Ω : List (NormalForm P)}
variable (d : ContractionBlock P (F++U) K) (hn : 2 ≤ d.gs.length)

/-- Arbitrary actual left contraction over native mix. Both premise selections
    and all endpoint matches are derived internally from its constructor data. -/
theorem left_atomized (f : G P U Δ) (g : G P F Λ)
    (cutLeft : G P Γ (d.C::Ξ)) (root : G P (d.C::Θ) Ω) :
    AtomizedReducesL cutLeft root (d.applyL hn _ (G.mix f g)) d.keep := by
  let p := d.selection (d.nonempty hn)
  have hb : p.block=d := d.selection_block _
  have hp : 2 ≤ p.arity := by
    have hc:=p.count
    have hg : p.gs.length=d.gs.length := congrArg (fun b => b.gs.length) hb
    omega
  have hSel : AtomizedReducesL cutLeft root (p.block.applyL (p.blockArity hp) _ (G.mix f g)) p.keep := by
    intro hat a hr
    exact selection_left_atomized p hp f g a hr hat
  have hw : p.block.applyL (p.blockArity hp) _ (G.mix f g) =
      d.applyL hn _ (G.mix f g) := ContractionBlock.applyL_congr hb _ _ _ _
  have hx : p.keep=d.keep := d.selection_keep hn
  rw [hw,hx] at hSel
  exact hSel

/-- Right contraction over native mix, independently typed and with the same
    internal complete positional split. -/
theorem right_atomized (f : G P Δ U) (g : G P Λ F)
    (root : G P Γ (d.C::Ξ)) (cutRight : G P (d.C::Θ) Ω) :
    AtomizedReducesR root cutRight (d.applyR hn _ (G.mix f g)) d.keep := by
  let p := d.selection (d.nonempty hn)
  have hb : p.block=d := d.selection_block _
  have hp : 2 ≤ p.arity := by
    have hc:=p.count
    have hg : p.gs.length=d.gs.length := congrArg (fun b => b.gs.length) hb
    omega
  have hSel : AtomizedReducesR root cutRight (p.block.applyR (p.blockArity hp) _ (G.mix f g)) p.keep := by
    intro hat a hr
    exact selection_right_atomized p hp f g a hr hat
  have hw : p.block.applyR (p.blockArity hp) _ (G.mix f g) =
      d.applyR hn _ (G.mix f g) := ContractionBlock.applyR_congr hb _ _ _ _
  have hx : p.keep=d.keep := d.selection_keep hn
  rw [hw,hx] at hSel
  exact hSel

end DosenPetric.Reduced.Gentzen.MixReducer
