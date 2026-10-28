module

public import DosenPetric.GentzenAtomizedLogicalInputReducers
public import DosenPetric.GentzenAtomizedOppositeLeaves
public import DosenPetric.GentzenAtomizedMix

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace OppositeUnaryReducer
variable {F K V Φ Ξ Ω Ψ : List (NormalForm P)}

theorem left_atomized (d : ContractionBlock P F K) (hn : 2≤d.gs.length)
    (f : G P F V) (hb : f.ruleKind.OppositeUnary .left)
    (cutLeft : G P Φ (d.C::Ξ)) (root : G P (d.C::Ω) Ψ) :
    AtomizedReducesL cutLeft root (d.applyL hn V f) d.keep := by
  cases f <;> simp only [G.ruleKind,G.RuleKind.OppositeUnary] at hb
  case thinR Δ Λ D f=>
    cases d with | mk C gs tail hu hk=>
      cases hu;cases hk
      exact W1.reducesL_atomized C D gs tail Δ Λ hn f cutLeft root
  case exchangeR Δ X Y Λ f=>
    cases d with | mk C gs tail hu hk=>
      cases hu;cases hk
      exact W1.Exchange.reducesL_atomized C gs tail Δ X Y Λ hn f cutLeft root
  case contractR D hs Λ hm f=>
    cases d with | mk C gs tail hu hk=>
      cases hu;cases hk
      exact W1.Contraction.reducesL_atomized C D gs hs tail Λ hn hm f cutLeft root
  case disjR Δ Λ A B f=>
    cases d with | mk C gs tail hu hk=>
      cases hu;cases hk
      exact W1.Logical.reducesL_atomized A B C gs tail Δ Λ hn f cutLeft root

theorem right_atomized (d : ContractionBlock P F K) (hn : 2≤d.gs.length)
    (f : G P V F) (hb : f.ruleKind.OppositeUnary .right)
    (root : G P Φ (d.C::Ξ)) (cutRight : G P (d.C::Ω) Ψ) :
    AtomizedReducesR root cutRight (d.applyR hn V f) d.keep := by
  cases f <;> simp only [G.ruleKind,G.RuleKind.OppositeUnary] at hb
  case thinL Γ Θ D f=>
    cases d with | mk C gs tail hu hk=>
      cases hu;cases hk
      exact W1.reducesR_atomized C D gs Γ Θ tail hn f root cutRight
  case exchangeL Γ X Y Θ f=>
    cases d with | mk C gs tail hu hk=>
      cases hu;cases hk
      exact W1.Exchange.reducesR_atomized C gs Γ X Y Θ tail hn f root cutRight
  case contractL D hs Θ hm f=>
    cases d with | mk C gs tail hu hk=>
      cases hu;cases hk
      exact W1.Contraction.reducesR_atomized D C hs gs Θ tail hm hn f root cutRight
  case conjL Γ Θ A B f=>
    cases d with | mk C gs tail hu hk=>
      cases hu;cases hk
      exact W1.Logical.reducesR_atomized A B C gs Γ Θ tail hn f root cutRight
end OppositeUnaryReducer
end DosenPetric.Reduced.Gentzen
