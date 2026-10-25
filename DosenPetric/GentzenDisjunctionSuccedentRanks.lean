module

public import DosenPetric.GentzenMixRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.G
universe u
variable {P : Type u} {Γ Θ F U : List (NormalForm P)} {A B : NormalForm P}
variable (f : G P (A::Γ) F) (g : G P (B::Θ) U)

theorem predecessors_disjL_f_right {C : NormalForm P} (a : At F C) :
    (disjL f g).predecessors .right (a.before U)=
      [⟨⟨_,_,f,Premise.disjL_left f g⟩,a⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change ((TraceRoute.before F U).fiber (a.before U)).map _++
    ((TraceRoute.shift F U).fiber (a.before U)).map _ = _
  rw [TraceRoute.fiber_before,TraceRoute.fiber_shift,At.splitAppend_before]
  rfl

theorem predecessors_disjL_g_right {C : NormalForm P} (a : At U C) :
    (disjL f g).predecessors .right (At.shift F a)=
      [⟨⟨_,_,g,Premise.disjL_right f g⟩,a⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change ((TraceRoute.before F U).fiber (At.shift F a)).map _++
    ((TraceRoute.shift F U).fiber (At.shift F a)).map _ = _
  rw [TraceRoute.fiber_before,TraceRoute.fiber_shift,At.splitAppend_shift]
  rfl

theorem rho_disjL_f_right {C : NormalForm P} (a : At F C) :
    (disjL f g).rho .right (a.before U)=1+f.rho .right a := by
  have h:=congrArg (fun us : List (Upper (disjL f g) .right C) =>
    1+(us.map (fun u => u.branch.proof.rho .right u.position)).sum) (predecessors_disjL_f_right f g a)
  exact ((disjL f g).rho_eq .right _).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using h)

theorem rho_disjL_g_right {C : NormalForm P} (a : At U C) :
    (disjL f g).rho .right (At.shift F a)=1+g.rho .right a := by
  have h:=congrArg (fun us : List (Upper (disjL f g) .right C) =>
    1+(us.map (fun u => u.branch.proof.rho .right u.position)).sum) (predecessors_disjL_g_right f g a)
  exact ((disjL f g).rho_eq .right _).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using h)
end DosenPetric.Reduced.Gentzen.G
