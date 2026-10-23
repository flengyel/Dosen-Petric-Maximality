module

public import DosenPetric.GentzenOppositeThinningRank

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace G

theorem predecessors_exchangeR_left (Γ Δ X Y Λ : List (NormalForm P))
    (f : G P Γ (Δ ++ X ++ Y ++ Λ)) {C : NormalForm P} (x : At Γ C) :
    (exchangeR Γ Δ X Y Λ f).predecessors .left x =
      [⟨⟨_,_,f,Premise.exchangeR Γ Δ X Y Λ f⟩,x⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change ((TraceRoute.ofMap Γ Γ (fun a => some a)).fiber x).map _ = _
  exact congrArg (List.map _) (TraceRoute.fiber_identity Γ x)

theorem predecessors_exchangeL_right (Γ X Y Θ Δ : List (NormalForm P))
    (f : G P (Γ ++ X ++ Y ++ Θ) Δ) {C : NormalForm P} (x : At Δ C) :
    (exchangeL Γ X Y Θ Δ f).predecessors .right x =
      [⟨⟨_,_,f,Premise.exchangeL Γ X Y Θ Δ f⟩,x⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change ((TraceRoute.ofMap Δ Δ (fun a => some a)).fiber x).map _ = _
  exact congrArg (List.map _) (TraceRoute.fiber_identity Δ x)

/-- Opposite-side exchange retains the exact selected position. -/
theorem rho_exchangeR_left (Γ Δ X Y Λ : List (NormalForm P))
    (f : G P Γ (Δ ++ X ++ Y ++ Λ)) {C : NormalForm P} (x : At Γ C) :
    (exchangeR Γ Δ X Y Λ f).rho .left x = 1 + f.rho .left x := by
  have hs := congrArg (fun us : List (Upper (exchangeR Γ Δ X Y Λ f) .left C) =>
    1 + (us.map (fun a => a.branch.proof.rho .left a.position)).sum)
    (predecessors_exchangeR_left Γ Δ X Y Λ f x)
  exact ((exchangeR Γ Δ X Y Λ f).rho_eq .left x).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using hs)

theorem rho_exchangeL_right (Γ X Y Θ Δ : List (NormalForm P))
    (f : G P (Γ ++ X ++ Y ++ Θ) Δ) {C : NormalForm P} (x : At Δ C) :
    (exchangeL Γ X Y Θ Δ f).rho .right x = 1 + f.rho .right x := by
  have hs := congrArg (fun us : List (Upper (exchangeL Γ X Y Θ Δ f) .right C) =>
    1 + (us.map (fun a => a.branch.proof.rho .right a.position)).sum)
    (predecessors_exchangeL_right Γ X Y Θ Δ f x)
  exact ((exchangeL Γ X Y Θ Δ f).rho_eq .right x).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using hs)

end G
end DosenPetric.Reduced.Gentzen
