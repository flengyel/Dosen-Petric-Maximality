module

public import DosenPetric.GentzenAtomizedReduction
public import DosenPetric.GentzenOppositeUnaryReducers
public import DosenPetric.GentzenThinningCommutationRank
public import DosenPetric.GentzenExchangeCommutationRank
public import DosenPetric.GentzenLogicalCommutationRank
public import DosenPetric.GentzenContractionCommutationRank

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace W1

theorem reducesL_atomized (C D : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Δ Λ : List (NormalForm P)) (hn : 2≤gs.length) (f : G P (repeated C gs ++ Θ) (Δ++Λ))
    {Φ Ξ Ω Ψ : List (NormalForm P)} (cutLeft : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    AtomizedReducesL cutLeft cutRight (oldL C D gs Θ Δ Λ hn f) (At.shift (gaps gs) (.here C Θ)) := by
  exact AtomizedReducesL.of_strict _ (cutFreeL C D gs Θ Δ Λ hn f).mpr (atomizedL C D gs Θ Δ Λ hn f).mpr (denoteL C D gs Θ Δ Λ hn f) (endpoint_decreasesL C D gs Θ Δ Λ hn f)

theorem reducesR_atomized (C D : NormalForm P) (gs : List (List (NormalForm P)))
    (Γ Θ Λ : List (NormalForm P)) (hn : 2≤gs.length) (f : G P (Γ++Θ) (repeated C gs ++ Λ))
    {Φ Ξ Ω Ψ : List (NormalForm P)} (cutLeft : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    AtomizedReducesR cutLeft cutRight (oldR C D gs Γ Θ Λ hn f) (At.shift (gaps gs) (.here C Λ)) := by
  exact AtomizedReducesR.of_strict _ (cutFreeR C D gs Γ Θ Λ hn f).mpr (atomizedR C D gs Γ Θ Λ hn f).mpr (denoteR C D gs Γ Θ Λ hn f) (endpoint_decreasesR C D gs Γ Θ Λ hn f)

end W1

namespace W1.Exchange

theorem reducesL_atomized (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Δ X Y Λ : List (NormalForm P)) (hn : 2≤gs.length) (f : G P (repeated C gs ++ Θ) (Δ++X++Y++Λ))
    {Φ Ξ Ω Ψ : List (NormalForm P)} (cutLeft : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    AtomizedReducesL cutLeft cutRight (oldL C gs Θ Δ X Y Λ hn f) (At.shift (gaps gs) (.here C Θ)) := by
  exact AtomizedReducesL.of_strict _ (cutFreeL C gs Θ Δ X Y Λ hn f).mpr (atomizedL C gs Θ Δ X Y Λ hn f).mpr (denoteL C gs Θ Δ X Y Λ hn f) (endpoint_decreasesL C gs Θ Δ X Y Λ hn f)

theorem reducesR_atomized (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Γ X Y Θ Λ : List (NormalForm P)) (hn : 2≤gs.length) (f : G P (Γ++X++Y++Θ) (repeated C gs ++ Λ))
    {Φ Ξ Ω Ψ : List (NormalForm P)} (cutLeft : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    AtomizedReducesR cutLeft cutRight (oldR C gs Γ X Y Θ Λ hn f) (At.shift (gaps gs) (.here C Λ)) := by
  exact AtomizedReducesR.of_strict _ (cutFreeR C gs Γ X Y Θ Λ hn f).mpr (atomizedR C gs Γ X Y Θ Λ hn f).mpr (denoteR C gs Γ X Y Θ Λ hn f) (endpoint_decreasesR C gs Γ X Y Θ Λ hn f)

end W1.Exchange

namespace W1.Logical

theorem reducesL_atomized (A B C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Δ Λ : List (NormalForm P)) (hn : 2≤gs.length) (f : G P (repeated C gs ++ Θ) (Δ++A::B::Λ))
    {Φ Ξ Ω Ψ : List (NormalForm P)} (cutLeft : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    AtomizedReducesL cutLeft cutRight (oldL A B C gs Θ Δ Λ hn f) (At.shift (gaps gs) (.here C Θ)) := by
  exact AtomizedReducesL.of_strict _ (cutFreeL A B C gs Θ Δ Λ hn f).mpr (atomizedL A B C gs Θ Δ Λ hn f).mpr (denoteL A B C gs Θ Δ Λ hn f) (endpoint_decreasesL A B C gs Θ Δ Λ hn f)

theorem reducesR_atomized (A B C : NormalForm P) (gs : List (List (NormalForm P)))
    (Γ Θ Λ : List (NormalForm P)) (hn : 2≤gs.length) (f : G P (Γ++A::B::Θ) (repeated C gs ++ Λ))
    {Φ Ξ Ω Ψ : List (NormalForm P)} (cutLeft : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    AtomizedReducesR cutLeft cutRight (oldR A B C gs Γ Θ Λ hn f) (At.shift (gaps gs) (.here C Λ)) := by
  exact AtomizedReducesR.of_strict _ (cutFreeR A B C gs Γ Θ Λ hn f).mpr (atomizedR A B C gs Γ Θ Λ hn f).mpr (denoteR A B C gs Γ Θ Λ hn f) (endpoint_decreasesR A B C gs Γ Θ Λ hn f)

end W1.Logical

namespace W1.Contraction
variable (C D : NormalForm P) (gs hs : List (List (NormalForm P)))
  (Θ Λ : List (NormalForm P)) (hn : 2≤gs.length) (hm : 2≤hs.length)
  (f : G P (repeated C gs++Θ) (repeated D hs++Λ))

theorem reducesL_atomized {Φ Ξ Ω Ψ : List (NormalForm P)}
    (cutLeft : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    AtomizedReducesL cutLeft cutRight (outerL C D gs hs Θ Λ hn hm f) (At.shift (gaps gs) (.here C Θ)) :=
  AtomizedReducesL.of_strict _ (cutFree C D gs hs Θ Λ hn hm f).mpr (atomized C D gs hs Θ Λ hn hm f).mpr (denote C D gs hs Θ Λ hn hm f)
    (left_directed_decrease C D gs hs Θ Λ hn hm f)

theorem reducesR_atomized {Φ Ξ Ω Ψ : List (NormalForm P)}
    (cutLeft : G P Φ (D::Ξ)) (cutRight : G P (D::Ω) Ψ) :
    AtomizedReducesR cutLeft cutRight (outerR C D gs hs Θ Λ hn hm f) (At.shift (gaps hs) (.here D Λ)) :=
  AtomizedReducesR.of_strict _ (cutFree C D gs hs Θ Λ hn hm f).mp (atomized C D gs hs Θ Λ hn hm f).mp (denote_reverse C D gs hs Θ Λ hn hm f)
    (right_directed_decrease C D gs hs Θ Λ hn hm f)
end W1.Contraction
end DosenPetric.Reduced.Gentzen
