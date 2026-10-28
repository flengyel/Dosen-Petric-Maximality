module

public import DosenPetric.GentzenAtomizedLogicalLeaves
public import DosenPetric.GentzenAtomizedOppositeLeaves
public import DosenPetric.GentzenAtomizedMix

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.LogicalInputReducer
universe u
variable {P : Type u} {C A B : NormalForm P} {Γ Θ K Δ Φ Ξ Ω Ψ : List (NormalForm P)}

theorem selection_left_atomized (q : ContractionSelection C (Γ++.conj A B::Θ) K) (hn : 2≤q.arity)
    (f : G P (Γ++A::B::Θ) Δ) (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Ψ) :
    AtomizedReducesL cutLeft root (q.performL Δ (G.conjL Γ Θ Δ A B f)) q.keep := by
  obtain ⟨g,m,hm⟩:=SelectionMask.append_exists q.mask
  cases m with
  | fixed D t=>
    exact FixedLogicalReducer.left_atomized g t q hn hm.symm f cutLeft root
  | pick t=>
    exact SelectedLogicalReducer.left_atomized g t q hn hm.symm f cutLeft root

theorem selection_right_atomized (q : ContractionSelection C (Γ++.disj A B::Θ) K) (hn : 2≤q.arity)
    (f : G P Δ (Γ++A::B::Θ)) (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    AtomizedReducesR root cutRight (q.performR Δ (G.disjR Δ Γ Θ A B f)) q.keep := by
  obtain ⟨g,m,hm⟩:=SelectionMask.append_exists q.mask
  cases m with
  | fixed D t=>
    exact FixedLogicalReducer.right_atomized g t q hn hm.symm f root cutRight
  | pick t=>
    exact SelectedLogicalReducer.right_atomized g t q hn hm.symm f root cutRight
end DosenPetric.Reduced.Gentzen.LogicalInputReducer
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace LogicalInputReducer
variable {C : NormalForm P} {F K V Φ Ξ Ω Ψ : List (NormalForm P)}
theorem input_left_atomized (q : ContractionSelection C F K) (hn : 2≤q.arity)
    (w : G P F V) (hb : w.ruleKind.LogicalUnary .left)
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Ψ) :
    AtomizedReducesL cutLeft root (q.performL V w) q.keep := by
  cases w <;> simp only [G.ruleKind,G.RuleKind.LogicalUnary] at hb
  case conjL Γ Θ A B t=>exact selection_left_atomized q hn t cutLeft root

theorem input_right_atomized (q : ContractionSelection C F K) (hn : 2≤q.arity)
    (w : G P V F) (hb : w.ruleKind.LogicalUnary .right)
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    AtomizedReducesR root cutRight (q.performR V w) q.keep := by
  cases w <;> simp only [G.ruleKind,G.RuleKind.LogicalUnary] at hb
  case disjR Γ Θ A B t=>exact selection_right_atomized q hn t root cutRight

theorem left_atomized (d : ContractionBlock P F K) (hn : 2≤d.gs.length)
    (w : G P F V) (hb : w.ruleKind.LogicalUnary .left)
    (cutLeft : G P Φ (d.C::Ξ)) (root : G P (d.C::Ω) Ψ) :
    AtomizedReducesL cutLeft root (d.applyL hn V w) d.keep := by
  let p:=d.selection (d.nonempty hn)
  have he : p.block=d:=d.selection_block _
  have hp : 2≤p.arity := by
    have h:=congrArg (fun b=>b.gs.length) he
    change p.gs.length=d.gs.length at h
    have hc:=p.count
    omega
  have h:=input_left_atomized p hp w hb cutLeft root
  have hw : p.performL _ w=d.applyL hn _ w :=
    (p.performL_eq_apply hp _).trans (ContractionBlock.applyL_congr he _ _ _ _)
  have hx : p.keep=d.keep:=d.selection_keep hn
  rw [hw,hx] at h
  exact h

theorem right_atomized (d : ContractionBlock P F K) (hn : 2≤d.gs.length)
    (w : G P V F) (hb : w.ruleKind.LogicalUnary .right)
    (root : G P Φ (d.C::Ξ)) (cutRight : G P (d.C::Ω) Ψ) :
    AtomizedReducesR root cutRight (d.applyR hn V w) d.keep := by
  let p:=d.selection (d.nonempty hn)
  have he : p.block=d:=d.selection_block _
  have hp : 2≤p.arity := by
    have h:=congrArg (fun b=>b.gs.length) he
    change p.gs.length=d.gs.length at h
    have hc:=p.count
    omega
  have h:=input_right_atomized p hp w hb root cutRight
  have hw : p.performR _ w=d.applyR hn _ w :=
    (p.performR_eq_apply hp _).trans (ContractionBlock.applyR_congr he _ _ _ _)
  have hx : p.keep=d.keep:=d.selection_keep hn
  rw [hw,hx] at h
  exact h
end LogicalInputReducer
end DosenPetric.Reduced.Gentzen
