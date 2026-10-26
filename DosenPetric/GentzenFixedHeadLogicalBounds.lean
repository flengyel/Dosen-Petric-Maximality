module

public import DosenPetric.GentzenUnaryRouteRepairBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionBound
universe u
variable {P : Type u} {C : NormalForm P} {k : Nat}

theorem conjL_head (Γ Θ Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P ((C::Γ)++A::B::Θ) Δ)
    (h : ContractionBound .left C k f (fun a=>a.index=0)) :
    ContractionBound .left C k (G.conjL (C::Γ) Θ Δ A B f) (fun a=>a.index=0) := by
  apply unary (Premise.conjL (C::Γ) Θ Δ A B f)
  · intro j;simpa only [G.branches,List.mem_singleton] using G.branches_complete j
  · intro x _ hx
    have ha:=(G.lowerContraction_iff_arity _ .left x).mp hx
    simp only [G.sourceArity] at ha
    split at ha <;> omega
  · apply h.mono
    rintro y ⟨x,hx,hy⟩
    have hx' : x=At.here C (Γ++.conj A B::Θ):=At.index_injective _ _ hx
    cases hx'
    have he:=At.fixed_injective (C::Γ) [A,B] [.conj A B] Θ y
      (At.here C (Γ++A::B::Θ)) (At.here C (Γ++.conj A B::Θ)) hy rfl
    exact congrArg At.index he

theorem disjR_head (Δ Γ Θ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Δ ((C::Γ)++A::B::Θ))
    (h : ContractionBound .right C k f (fun a=>a.index=0)) :
    ContractionBound .right C k (G.disjR Δ (C::Γ) Θ A B f) (fun a=>a.index=0) := by
  apply unary (Premise.disjR Δ (C::Γ) Θ A B f)
  · intro j;simpa only [G.branches,List.mem_singleton] using G.branches_complete j
  · intro x _ hx
    have ha:=(G.lowerContraction_iff_arity _ .right x).mp hx
    simp only [G.sourceArity] at ha
    split at ha <;> omega
  · apply h.mono
    rintro y ⟨x,hx,hy⟩
    have hx' : x=At.here C (Γ++.disj A B::Θ):=At.index_injective _ _ hx
    cases hx'
    have he:=At.fixed_injective (C::Γ) [A,B] [.disj A B] Θ y
      (At.here C (Γ++A::B::Θ)) (At.here C (Γ++.disj A B::Θ)) hy rfl
    exact congrArg At.index he
end DosenPetric.Reduced.Gentzen.ContractionBound
