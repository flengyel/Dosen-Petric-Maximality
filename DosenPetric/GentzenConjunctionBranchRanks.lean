module

public import DosenPetric.GentzenBinaryLogicalRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.G
universe u
variable {P : Type u} {Γ Θ F U : List (NormalForm P)} {A B : NormalForm P}
variable (f : G P Γ (A::F)) (g : G P Θ (B::U))

theorem predecessors_conjR_f {C : NormalForm P} (a : At F C) :
    (conjR f g).predecessors .right (.there (a.before U))=
      [⟨⟨_,_,f,Premise.conjR_left f g⟩,.there a⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [Premise.conjR_left_right_route,Premise.conjR_right_right_route]
  change ((TraceRoute.wrap (.conj A B) A (TraceRoute.before F U)).fiber (.there (a.before U))).map _++
    ((TraceRoute.wrap (.conj A B) B (TraceRoute.shift F U)).fiber (.there (a.before U))).map _ = _
  rw [TraceRoute.fiber_wrap_there,TraceRoute.fiber_wrap_there,
    TraceRoute.fiber_before,TraceRoute.fiber_shift,At.splitAppend_before]
  rfl

theorem predecessors_conjR_g {C : NormalForm P} (a : At U C) :
    (conjR f g).predecessors .right (.there (At.shift F a))=
      [⟨⟨_,_,g,Premise.conjR_right f g⟩,.there a⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [Premise.conjR_left_right_route,Premise.conjR_right_right_route]
  change ((TraceRoute.wrap (.conj A B) A (TraceRoute.before F U)).fiber (.there (At.shift F a))).map _++
    ((TraceRoute.wrap (.conj A B) B (TraceRoute.shift F U)).fiber (.there (At.shift F a))).map _ = _
  rw [TraceRoute.fiber_wrap_there,TraceRoute.fiber_wrap_there,
    TraceRoute.fiber_before,TraceRoute.fiber_shift,At.splitAppend_shift]
  rfl

theorem rho_conjR_f {C : NormalForm P} (a : At F C) :
    (conjR f g).rho .right (.there (a.before U))=1+f.rho .right (.there a) := by
  have h:=congrArg (fun us : List (Upper (conjR f g) .right C) =>
    1+(us.map (fun u => u.branch.proof.rho .right u.position)).sum) (predecessors_conjR_f f g a)
  exact ((conjR f g).rho_eq .right _).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using h)

theorem rho_conjR_g {C : NormalForm P} (a : At U C) :
    (conjR f g).rho .right (.there (At.shift F a))=1+g.rho .right (.there a) := by
  have h:=congrArg (fun us : List (Upper (conjR f g) .right C) =>
    1+(us.map (fun u => u.branch.proof.rho .right u.position)).sum) (predecessors_conjR_g f g a)
  exact ((conjR f g).rho_eq .right _).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using h)

theorem rho_conjR_principal :
    (conjR f g).rho .right (.here (.conj A B) (F++U))=1 := rho_leaf _ .right _ (by rfl)

end DosenPetric.Reduced.Gentzen.G
