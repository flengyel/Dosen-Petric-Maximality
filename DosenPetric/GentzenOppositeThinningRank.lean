module

public import DosenPetric.GentzenClassifiedRank

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace G

theorem predecessors_thinR_left (Γ Δ Λ : List (NormalForm P)) (D : NormalForm P)
    (f : G P Γ (Δ ++ Λ)) {C : NormalForm P} (x : At Γ C) :
    (thinR Γ Δ Λ D f).predecessors .left x =
      [⟨⟨_,_,f,Premise.thinR Γ Δ Λ D f⟩,x⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change ((TraceRoute.ofMap Γ Γ (fun a => some a)).fiber x).map _ = _
  exact congrArg (List.map _) (TraceRoute.fiber_identity Γ x)

theorem predecessors_thinL_right (Γ Θ Δ : List (NormalForm P)) (D : NormalForm P)
    (f : G P (Γ ++ Θ) Δ) {C : NormalForm P} (x : At Δ C) :
    (thinL Γ Θ Δ D f).predecessors .right x =
      [⟨⟨_,_,f,Premise.thinL Γ Θ Δ D f⟩,x⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change ((TraceRoute.ofMap Δ Δ (fun a => some a)).fiber x).map _ = _
  exact congrArg (List.map _) (TraceRoute.fiber_identity Δ x)

/-- Opposite-side thinning retains the exact selected position. -/
theorem rho_thinR_left (Γ Δ Λ : List (NormalForm P)) (D : NormalForm P)
    (f : G P Γ (Δ ++ Λ)) {C : NormalForm P} (x : At Γ C) :
    (thinR Γ Δ Λ D f).rho .left x = 1 + f.rho .left x := by
  have hs := congrArg (fun us : List (Upper (thinR Γ Δ Λ D f) .left C) =>
    1 + (us.map (fun a => a.branch.proof.rho .left a.position)).sum)
    (predecessors_thinR_left Γ Δ Λ D f x)
  exact ((thinR Γ Δ Λ D f).rho_eq .left x).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using hs)

theorem rho_thinL_right (Γ Θ Δ : List (NormalForm P)) (D : NormalForm P)
    (f : G P (Γ ++ Θ) Δ) {C : NormalForm P} (x : At Δ C) :
    (thinL Γ Θ Δ D f).rho .right x = 1 + f.rho .right x := by
  have hs := congrArg (fun us : List (Upper (thinL Γ Θ Δ D f) .right C) =>
    1 + (us.map (fun a => a.branch.proof.rho .right a.position)).sum)
    (predecessors_thinL_right Γ Θ Δ D f x)
  exact ((thinL Γ Θ Δ D f).rho_eq .right x).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using hs)

/-- Each list entry contributes one node, with no identification of entries. -/
theorem sum_map_one_add {α : Type u} (xs : List α) (r : α → Nat) :
    (xs.map (fun x => 1 + r x)).sum = (xs.map r).sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

end G
end DosenPetric.Reduced.Gentzen
