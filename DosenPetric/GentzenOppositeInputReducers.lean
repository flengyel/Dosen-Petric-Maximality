module

public import DosenPetric.GentzenOppositeUnaryReducers
public import DosenPetric.GentzenUnrestrictedExchangeReducers

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace G.RuleKind
/-- The four unary rules acting on the sequent side opposite the contraction. -/
def OppositeUnary : SequentSide→G.RuleKind→Prop
  | .left,.thinR | .left,.exchangeR | .left,.contractR | .left,.disjR=>True
  | .right,.thinL | .right,.exchangeL | .right,.contractL | .right,.conjL=>True
  | _,_=>False
end G.RuleKind

namespace OppositeUnaryReducer
variable {F K V Φ Ξ Ω Ψ : List (NormalForm P)}

theorem left (d : ContractionBlock P F K) (hn : 2≤d.gs.length)
    (f : G P F V) (hb : f.ruleKind.OppositeUnary .left)
    (cutLeft : G P Φ (d.C::Ξ)) (root : G P (d.C::Ω) Ψ) :
    ReducesL cutLeft root (d.applyL hn V f) d.keep := by
  cases f <;> simp only [G.ruleKind,G.RuleKind.OppositeUnary] at hb
  case thinR Δ Λ D f=>
    cases d with | mk C gs tail hu hk=>
      cases hu;cases hk
      exact W1.reducesL C D gs tail Δ Λ hn f cutLeft root
  case exchangeR Δ X Y Λ f=>
    cases d with | mk C gs tail hu hk=>
      cases hu;cases hk
      exact W1.Exchange.reducesL C gs tail Δ X Y Λ hn f cutLeft root
  case contractR D hs Λ hm f=>
    cases d with | mk C gs tail hu hk=>
      cases hu;cases hk
      exact W1.Contraction.reducesL C D gs hs tail Λ hn hm f cutLeft root
  case disjR Δ Λ A B f=>
    cases d with | mk C gs tail hu hk=>
      cases hu;cases hk
      exact W1.Logical.reducesL A B C gs tail Δ Λ hn f cutLeft root

theorem right (d : ContractionBlock P F K) (hn : 2≤d.gs.length)
    (f : G P V F) (hb : f.ruleKind.OppositeUnary .right)
    (root : G P Φ (d.C::Ξ)) (cutRight : G P (d.C::Ω) Ψ) :
    ReducesR root cutRight (d.applyR hn V f) d.keep := by
  cases f <;> simp only [G.ruleKind,G.RuleKind.OppositeUnary] at hb
  case thinL Γ Θ D f=>
    cases d with | mk C gs tail hu hk=>
      cases hu;cases hk
      exact W1.reducesR C D gs Γ Θ tail hn f root cutRight
  case exchangeL Γ X Y Θ f=>
    cases d with | mk C gs tail hu hk=>
      cases hu;cases hk
      exact W1.Exchange.reducesR C gs Γ X Y Θ tail hn f root cutRight
  case contractL D hs Θ hm f=>
    cases d with | mk C gs tail hu hk=>
      cases hu;cases hk
      exact W1.Contraction.reducesR D C hs gs Θ tail hm hn f root cutRight
  case conjL Γ Θ A B f=>
    cases d with | mk C gs tail hu hk=>
      cases hu;cases hk
      exact W1.Logical.reducesR A B C gs Γ Θ tail hn f root cutRight
end OppositeUnaryReducer
end DosenPetric.Reduced.Gentzen
