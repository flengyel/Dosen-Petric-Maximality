module

public import DosenPetric.GentzenAtomizedBinaryInputReducers
public import DosenPetric.GentzenAtomizedOppositeLeaves
public import DosenPetric.GentzenAtomizedMix

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.AllInputReducer
universe u
variable {P : Type u} {F K V Φ Ξ Ω Ψ : List (NormalForm P)}

/-- Every actual input constructor of a left contraction. -/
theorem left_atomized (d : ContractionBlock P F K) (hn : 2≤d.gs.length)
    (w : G P F V) (cutLeft : G P Φ (d.C::Ξ)) (root : G P (d.C::Ω) Ψ) :
    AtomizedReducesL cutLeft root (d.applyL hn V w) d.keep := by
  have hb:=d.not_basisL hn w
  cases w <;> first
    | exact BinaryReducer.left_atomized d hn _ (by trivial) cutLeft root
    | exact OppositeUnaryReducer.left_atomized d hn _ (by trivial) cutLeft root
    | exact RoutingInputReducer.left_atomized d hn _ (by trivial) cutLeft root
    | exact LogicalInputReducer.left_atomized d hn _ (by trivial) cutLeft root
    | exact False.elim (hb (by trivial))

/-- Every actual input constructor of a right contraction. -/
theorem right_atomized (d : ContractionBlock P F K) (hn : 2≤d.gs.length)
    (w : G P V F) (root : G P Φ (d.C::Ξ)) (cutRight : G P (d.C::Ω) Ψ) :
    AtomizedReducesR root cutRight (d.applyR hn V w) d.keep := by
  have hb:=d.not_basisR hn w
  cases w <;> first
    | exact BinaryReducer.right_atomized d hn _ (by trivial) root cutRight
    | exact OppositeUnaryReducer.right_atomized d hn _ (by trivial) root cutRight
    | exact RoutingInputReducer.right_atomized d hn _ (by trivial) root cutRight
    | exact LogicalInputReducer.right_atomized d hn _ (by trivial) root cutRight
    | exact False.elim (hb (by trivial))
end DosenPetric.Reduced.Gentzen.AllInputReducer
