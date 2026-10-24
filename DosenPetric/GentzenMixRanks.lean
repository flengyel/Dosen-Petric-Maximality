module

public import DosenPetric.GentzenContractionAppend
public import DosenPetric.GentzenOppositeContractionRank

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace G
variable {Γ Θ Δ Λ : List (NormalForm P)} (f : G P Γ Δ) (g : G P Θ Λ)

theorem predecessors_mix_g_left {A : NormalForm P} (a : At Θ A) :
    (mix f g).predecessors .left (a.before Γ) =
      [⟨⟨_,_,g,Premise.mix_right f g⟩,a⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change ((TraceRoute.shift Θ Γ).fiber (a.before Γ)).map _++
    ((TraceRoute.before Θ Γ).fiber (a.before Γ)).map _ = _
  rw [TraceRoute.fiber_shift,TraceRoute.fiber_before,At.splitAppend_before]
  rfl
theorem rho_mix_g_left {A : NormalForm P} (a : At Θ A) :
    (mix f g).rho .left (a.before Γ) = 1+g.rho .left a := by
  have h := congrArg (fun us : List (Upper (mix f g) .left A) =>
    1+(us.map (fun v => v.branch.proof.rho .left v.position)).sum)
    (predecessors_mix_g_left f g a)
  exact ((mix f g).rho_eq .left _).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using h)

theorem predecessors_mix_f_left {A : NormalForm P} (a : At Γ A) :
    (mix f g).predecessors .left (At.shift Θ a) =
      [⟨⟨_,_,f,Premise.mix_left f g⟩,a⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change ((TraceRoute.shift Θ Γ).fiber (At.shift Θ a)).map _++
    ((TraceRoute.before Θ Γ).fiber (At.shift Θ a)).map _ = _
  rw [TraceRoute.fiber_shift,TraceRoute.fiber_before,At.splitAppend_shift]
  rfl
theorem rho_mix_f_left {A : NormalForm P} (a : At Γ A) :
    (mix f g).rho .left (At.shift Θ a) = 1+f.rho .left a := by
  have h := congrArg (fun us : List (Upper (mix f g) .left A) =>
    1+(us.map (fun v => v.branch.proof.rho .left v.position)).sum)
    (predecessors_mix_f_left f g a)
  exact ((mix f g).rho_eq .left _).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using h)

theorem predecessors_mix_g_right {A : NormalForm P} (a : At Λ A) :
    (mix f g).predecessors .right (a.before Δ) =
      [⟨⟨_,_,g,Premise.mix_right f g⟩,a⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change ((TraceRoute.shift Λ Δ).fiber (a.before Δ)).map _++
    ((TraceRoute.before Λ Δ).fiber (a.before Δ)).map _ = _
  rw [TraceRoute.fiber_shift,TraceRoute.fiber_before,At.splitAppend_before]
  rfl
theorem rho_mix_g_right {A : NormalForm P} (a : At Λ A) :
    (mix f g).rho .right (a.before Δ) = 1+g.rho .right a := by
  have h := congrArg (fun us : List (Upper (mix f g) .right A) =>
    1+(us.map (fun v => v.branch.proof.rho .right v.position)).sum)
    (predecessors_mix_g_right f g a)
  exact ((mix f g).rho_eq .right _).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using h)

theorem predecessors_mix_f_right {A : NormalForm P} (a : At Δ A) :
    (mix f g).predecessors .right (At.shift Λ a) =
      [⟨⟨_,_,f,Premise.mix_left f g⟩,a⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change ((TraceRoute.shift Λ Δ).fiber (At.shift Λ a)).map _++
    ((TraceRoute.before Λ Δ).fiber (At.shift Λ a)).map _ = _
  rw [TraceRoute.fiber_shift,TraceRoute.fiber_before,At.splitAppend_shift]
  rfl
theorem rho_mix_f_right {A : NormalForm P} (a : At Δ A) :
    (mix f g).rho .right (At.shift Λ a) = 1+f.rho .right a := by
  have h := congrArg (fun us : List (Upper (mix f g) .right A) =>
    1+(us.map (fun v => v.branch.proof.rho .right v.position)).sum)
    (predecessors_mix_f_right f g a)
  exact ((mix f g).rho_eq .right _).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using h)

end G
namespace ContractionBlock
variable {F K : List (NormalForm P)} (d : ContractionBlock P F K)
theorem oppositeL (hn : 2 ≤ d.gs.length) {Δ : List (NormalForm P)} (f : G P F Δ)
    {A : NormalForm P} (a : At Δ A) : (d.applyL hn Δ f).rho .right a = 1+f.rho .right a := by
  cases d with
  | mk C gs tail hu hl =>
    cases hu; cases hl
    exact G.rho_contractL_right C gs tail Δ hn f a
theorem oppositeR (hn : 2 ≤ d.gs.length) {Γ : List (NormalForm P)} (f : G P Γ F)
    {A : NormalForm P} (a : At Γ A) : (d.applyR hn Γ f).rho .left a = 1+f.rho .left a := by
  cases d with
  | mk C gs tail hu hl =>
    cases hu; cases hl
    exact G.rho_contractR_left Γ C gs tail hn f a
end ContractionBlock
end DosenPetric.Reduced.Gentzen
