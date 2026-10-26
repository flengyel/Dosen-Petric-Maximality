module

public import DosenPetric.GentzenLogicalInputReducers
public import DosenPetric.GentzenRoutingInputReducers
public import DosenPetric.GentzenOppositeInputReducers
public import DosenPetric.GentzenBinaryInputReducers
public import DosenPetric.GentzenReducibilityTerminalOne

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.AllInputReducer
universe u
variable {P : Type u} {F K V Φ Ξ Ω Ψ : List (NormalForm P)}

/-- Every actual input constructor of a left contraction. -/
theorem left (d : ContractionBlock P F K) (hn : 2≤d.gs.length)
    (w : G P F V) (cutLeft : G P Φ (d.C::Ξ)) (root : G P (d.C::Ω) Ψ) :
    ReducesL cutLeft root (d.applyL hn V w) d.keep := by
  have hb:=d.not_basisL hn w
  cases w <;> first
    | exact BinaryReducer.left d hn _ (by trivial) cutLeft root
    | exact OppositeUnaryReducer.left d hn _ (by trivial) cutLeft root
    | exact RoutingInputReducer.left d hn _ (by trivial) cutLeft root
    | exact LogicalInputReducer.left d hn _ (by trivial) cutLeft root
    | exact False.elim (hb (by trivial))

/-- Every actual input constructor of a right contraction. -/
theorem right (d : ContractionBlock P F K) (hn : 2≤d.gs.length)
    (w : G P V F) (root : G P Φ (d.C::Ξ)) (cutRight : G P (d.C::Ω) Ψ) :
    ReducesR root cutRight (d.applyR hn V w) d.keep := by
  have hb:=d.not_basisR hn w
  cases w <;> first
    | exact BinaryReducer.right d hn _ (by trivial) root cutRight
    | exact OppositeUnaryReducer.right d hn _ (by trivial) root cutRight
    | exact RoutingInputReducer.right d hn _ (by trivial) root cutRight
    | exact LogicalInputReducer.right d hn _ (by trivial) root cutRight
    | exact False.elim (hb (by trivial))
end DosenPetric.Reduced.Gentzen.AllInputReducer
