module

public import DosenPetric.GentzenMixRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.G
universe u
variable {P : Type u} {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
variable (f : G P (A::Γ) Δ) (g : G P (B::Θ) Λ)

theorem predecessors_disjL_f {C : NormalForm P} (a : At Γ C) :
    (disjL f g).predecessors .left (.there (a.before Θ))=
      [⟨⟨_,_,f,Premise.disjL_left f g⟩,.there a⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [Premise.disjL_left_left_route,Premise.disjL_right_left_route]
  change ((TraceRoute.wrap (.disj A B) A (TraceRoute.before Γ Θ)).fiber (.there (a.before Θ))).map _++
    ((TraceRoute.wrap (.disj A B) B (TraceRoute.shift Γ Θ)).fiber (.there (a.before Θ))).map _ = _
  rw [TraceRoute.fiber_wrap_there,TraceRoute.fiber_wrap_there,
    TraceRoute.fiber_before,TraceRoute.fiber_shift,At.splitAppend_before]
  rfl

theorem predecessors_disjL_g {C : NormalForm P} (a : At Θ C) :
    (disjL f g).predecessors .left (.there (At.shift Γ a))=
      [⟨⟨_,_,g,Premise.disjL_right f g⟩,.there a⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [Premise.disjL_left_left_route,Premise.disjL_right_left_route]
  change ((TraceRoute.wrap (.disj A B) A (TraceRoute.before Γ Θ)).fiber (.there (At.shift Γ a))).map _++
    ((TraceRoute.wrap (.disj A B) B (TraceRoute.shift Γ Θ)).fiber (.there (At.shift Γ a))).map _ = _
  rw [TraceRoute.fiber_wrap_there,TraceRoute.fiber_wrap_there,
    TraceRoute.fiber_before,TraceRoute.fiber_shift,At.splitAppend_shift]
  rfl

theorem rho_disjL_f {C : NormalForm P} (a : At Γ C) :
    (disjL f g).rho .left (.there (a.before Θ))=1+f.rho .left (.there a) := by
  have h:=congrArg (fun us : List (Upper (disjL f g) .left C) =>
    1+(us.map (fun u => u.branch.proof.rho .left u.position)).sum) (predecessors_disjL_f f g a)
  exact ((disjL f g).rho_eq .left _).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using h)

theorem rho_disjL_g {C : NormalForm P} (a : At Θ C) :
    (disjL f g).rho .left (.there (At.shift Γ a))=1+g.rho .left (.there a) := by
  have h:=congrArg (fun us : List (Upper (disjL f g) .left C) =>
    1+(us.map (fun u => u.branch.proof.rho .left u.position)).sum) (predecessors_disjL_g f g a)
  exact ((disjL f g).rho_eq .left _).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using h)

end DosenPetric.Reduced.Gentzen.G
