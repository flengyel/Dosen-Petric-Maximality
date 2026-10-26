module

public import DosenPetric.GentzenAllInputReducers

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {C : NormalForm P} {Φ Ξ Ω Ψ U V : List (NormalForm P)}

/-- Full left Reducibility: all actual containing addresses and every eligible
contraction descendant in the replacement, with no input-rule restriction. -/
theorem reducibility_left (f : G P Φ (C::Ξ)) (g : G P (C::Ω) Ψ)
    (w : G P U V) (x : At U C) : ReducesL f g w x := by
  intro a hr
  have hl:=hr.2.1.2
  change w.LowerContraction .left x at hl
  cases hl with
  | left C gs Θ Δ hn t=>
    let d : ContractionBlock P (repeated C gs++Θ) (gaps gs++C::Θ):=
      ⟨C,gs,Θ,rfl,rfl⟩
    exact AllInputReducer.left d hn t f g a hr

/-- Full right Reducibility, independently typed on succedent positions. -/
theorem reducibility_right (f : G P Φ (C::Ξ)) (g : G P (C::Ω) Ψ)
    (w : G P U V) (x : At V C) : ReducesR f g w x := by
  intro a hr
  have hl:=hr.2.1.2
  change w.LowerContraction .right x at hl
  cases hl with
  | right Γ C gs Λ hn t=>
    let d : ContractionBlock P (repeated C gs++Λ) (gaps gs++C::Λ):=
      ⟨C,gs,Λ,rfl,rfl⟩
    exact AllInputReducer.right d hn t f g a hr
end DosenPetric.Reduced.Gentzen
