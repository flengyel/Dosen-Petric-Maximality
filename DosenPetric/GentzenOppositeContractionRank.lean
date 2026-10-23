module

public import DosenPetric.GentzenOppositeThinningRank

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace G

theorem predecessors_contractR_left (Γ : List (NormalForm P)) (D : NormalForm P)
    (hs : List (List (NormalForm P))) (Λ : List (NormalForm P)) (hm : 2 ≤ hs.length)
    (f : G P Γ (repeated D hs ++ Λ)) {A : NormalForm P} (x : At Γ A) :
    (contractR Γ D hs Λ hm f).predecessors .left x =
      [⟨⟨_,_,f,Premise.contractR Γ D hs Λ hm f⟩,x⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change ((TraceRoute.ofMap Γ Γ (fun a => some a)).fiber x).map _ = _
  exact congrArg (List.map _) (TraceRoute.fiber_identity Γ x)

theorem predecessors_contractL_right (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Δ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (f : G P (repeated C gs ++ Θ) Δ) {A : NormalForm P} (y : At Δ A) :
    (contractL C gs Θ Δ hn f).predecessors .right y =
      [⟨⟨_,_,f,Premise.contractL C gs Θ Δ hn f⟩,y⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change ((TraceRoute.ofMap Δ Δ (fun a => some a)).fiber y).map _ = _
  exact congrArg (List.map _) (TraceRoute.fiber_identity Δ y)

/-- A contraction branches only on its selected side, not on the opposite side. -/
theorem rho_contractR_left (Γ : List (NormalForm P)) (D : NormalForm P)
    (hs : List (List (NormalForm P))) (Λ : List (NormalForm P)) (hm : 2 ≤ hs.length)
    (f : G P Γ (repeated D hs ++ Λ)) {A : NormalForm P} (x : At Γ A) :
    (contractR Γ D hs Λ hm f).rho .left x = 1 + f.rho .left x := by
  have he := congrArg (fun us : List (Upper (contractR Γ D hs Λ hm f) .left A) =>
    1 + (us.map (fun a => a.branch.proof.rho .left a.position)).sum)
    (predecessors_contractR_left Γ D hs Λ hm f x)
  exact ((contractR Γ D hs Λ hm f).rho_eq .left x).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using he)

theorem rho_contractL_right (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Δ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (f : G P (repeated C gs ++ Θ) Δ) {A : NormalForm P} (y : At Δ A) :
    (contractL C gs Θ Δ hn f).rho .right y = 1 + f.rho .right y := by
  have he := congrArg (fun us : List (Upper (contractL C gs Θ Δ hn f) .right A) =>
    1 + (us.map (fun a => a.branch.proof.rho .right a.position)).sum)
    (predecessors_contractL_right C gs Θ Δ hn f y)
  exact ((contractL C gs Θ Δ hn f).rho_eq .right y).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using he)

end G
end DosenPetric.Reduced.Gentzen
