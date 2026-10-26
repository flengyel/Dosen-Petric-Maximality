module

public import DosenPetric.GentzenUnaryRouteProducers

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace G.RuleKind

def RoutingUnary : SequentSide→G.RuleKind→Prop
  | .left,.exchangeL | .left,.thinL | .left,.contractL=>True
  | .right,.exchangeR | .right,.thinR | .right,.contractR=>True
  | _,_=>False
end G.RuleKind
namespace RoutingInputReducer
variable {C : NormalForm P} {F K V Φ Ξ Ω Ψ : List (NormalForm P)}

theorem selection_left (q : ContractionSelection C F K) (hn : 2≤q.arity)
    (w : G P F V) (hb : w.ruleKind.RoutingUnary .left)
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Ψ) :
    ReducesL cutLeft root (q.performL V w) q.keep := by
  cases w <;> simp only [G.ruleKind,G.RuleKind.RoutingUnary] at hb
  case exchangeL Γ X Y Θ t=>
    apply UnaryRouteReducer.left_of_route q hn _ t
      (Premise.exchangeL Γ X Y Θ V t) (Route.exchange Γ X Y Θ) rfl
      (fun a=>by rw [Route.exchange_get];rfl) _ rfl cutLeft root
    rw [Route.exchange_product]
    rfl
  case thinL Γ Θ A t=>
    exact UnaryRouteReducer.left_of_route q hn _ t (Premise.thinL Γ Θ V A t)
      (Route.thin Γ Θ A) rfl (fun _=>rfl) rfl rfl cutLeft root
  case contractL A gs Θ hm t=>
    exact UnaryRouteReducer.left_of_route q hn _ t (Premise.contractL A gs Θ V hm t)
      (copies A gs Θ) rfl (fun _=>rfl) rfl rfl cutLeft root

theorem selection_right (q : ContractionSelection C F K) (hn : 2≤q.arity)
    (w : G P V F) (hb : w.ruleKind.RoutingUnary .right)
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    ReducesR root cutRight (q.performR V w) q.keep := by
  cases w <;> simp only [G.ruleKind,G.RuleKind.RoutingUnary] at hb
  case exchangeR Δ X Y Λ t=>
    apply UnaryRouteReducer.right_of_route q hn _ t
      (Premise.exchangeR V Δ X Y Λ t) (Route.exchange Δ X Y Λ) rfl
      (fun a=>by rw [Route.exchange_get];rfl) _ rfl root cutRight
    rw [Route.exchange_coproduct]
    rfl
  case thinR Δ Λ A t=>
    exact UnaryRouteReducer.right_of_route q hn _ t (Premise.thinR V Δ Λ A t)
      (Route.thin Δ Λ A) rfl (fun _=>rfl) rfl rfl root cutRight
  case contractR A gs Λ hm t=>
    exact UnaryRouteReducer.right_of_route q hn _ t (Premise.contractR V A gs Λ hm t)
      (copies A gs Λ) rfl (fun _=>rfl) rfl rfl root cutRight

theorem left (d : ContractionBlock P F K) (hn : 2≤d.gs.length)
    (w : G P F V) (hb : w.ruleKind.RoutingUnary .left)
    (cutLeft : G P Φ (d.C::Ξ)) (root : G P (d.C::Ω) Ψ) :
    ReducesL cutLeft root (d.applyL hn V w) d.keep := by
  let p:=d.selection (d.nonempty hn)
  have he : p.block=d:=d.selection_block _
  have hp : 2≤p.arity := by
    have h:=congrArg (fun b=>b.gs.length) he
    change p.gs.length=d.gs.length at h
    have hc:=p.count
    omega
  have h:=selection_left p hp w hb cutLeft root
  have hw : p.performL _ w=d.applyL hn _ w :=
    (p.performL_eq_apply hp _).trans (ContractionBlock.applyL_congr he _ _ _ _)
  have hx : p.keep=d.keep:=d.selection_keep hn
  rw [hw,hx] at h
  exact h

theorem right (d : ContractionBlock P F K) (hn : 2≤d.gs.length)
    (w : G P V F) (hb : w.ruleKind.RoutingUnary .right)
    (root : G P Φ (d.C::Ξ)) (cutRight : G P (d.C::Ω) Ψ) :
    ReducesR root cutRight (d.applyR hn V w) d.keep := by
  let p:=d.selection (d.nonempty hn)
  have he : p.block=d:=d.selection_block _
  have hp : 2≤p.arity := by
    have h:=congrArg (fun b=>b.gs.length) he
    change p.gs.length=d.gs.length at h
    have hc:=p.count
    omega
  have h:=selection_right p hp w hb root cutRight
  have hw : p.performR _ w=d.applyR hn _ w :=
    (p.performR_eq_apply hp _).trans (ContractionBlock.applyR_congr he _ _ _ _)
  have hx : p.keep=d.keep:=d.selection_keep hn
  rw [hw,hx] at h
  exact h
end RoutingInputReducer
end DosenPetric.Reduced.Gentzen
