module

public import DosenPetric.GentzenSequentialConjunctionNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem terminal_logical_head_square (o : Op) (F : List (NormalForm P)) (A B : NormalForm P) :
    (side P o).comp ((BinaryMix.swapWhole F [o.formula A B]).arrow o) (logicalSide o F [] A B) =
      (side P o).comp (logicalSide o [] F A B) ((BinaryMix.swapWhole F [A,B]).arrow o) := by
  let S := side P o
  apply side_ext o
  intro E a
  cases At.cases_append F [A,B] a with
  | inl ha =>
    obtain ⟨a,rfl⟩ := ha
    rw [S.assoc,logical_prefix,ExchangeScript.component,BinaryMix.swapWhole_before,
      S.assoc,ExchangeScript.component,BinaryMix.swapWhole_before]
    change component o (At.there a) = S.comp (logicalSide o [] F A B)
      (component o (At.shift [A,B] a))
    exact (logical_tail o [] F A B a).symm
  | inr ha =>
    obtain ⟨a,rfl⟩ := ha
    cases a with
    | here =>
      rw [S.assoc,logical_first,← S.assoc,ExchangeScript.component,BinaryMix.swapWhole_shift,
        S.assoc,ExchangeScript.component,BinaryMix.swapWhole_shift]
      exact (logical_first o [] F A B).symm
    | there a => cases a with
      | here =>
        rw [S.assoc,logical_second,← S.assoc,ExchangeScript.component,BinaryMix.swapWhole_shift,
          S.assoc,ExchangeScript.component,BinaryMix.swapWhole_shift]
        exact (logical_second o [] F A B).symm
      | there a => cases a

namespace ExchangeScript

theorem structural_singleFiber {F U : List (NormalForm P)} (p : ExchangeScript P F U)
    {C : NormalForm P} (x : At F C) (y : At U C) (he : p.get y = x) :
    p.structural.route.SingleFiber x y := by
  apply Route.singleFiber_of_unique
  · rw [StructuralProgram.route_get,structural_get,he]
  · intro b hb
    apply p.injective
    rw [he]
    simpa only [StructuralProgram.route_get,structural_get] using hb

end ExchangeScript
end DosenPetric.Reduced.Gentzen
