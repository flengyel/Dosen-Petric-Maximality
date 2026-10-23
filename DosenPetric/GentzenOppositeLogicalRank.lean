module

public import DosenPetric.GentzenOppositeContractionRank

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace G

theorem predecessors_disjR_left (Γ Δ Λ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ (Δ ++ A :: B :: Λ)) {C : NormalForm P} (x : At Γ C) :
    (disjR Γ Δ Λ A B f).predecessors .left x =
      [⟨⟨_,_,f,Premise.disjR Γ Δ Λ A B f⟩,x⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change ((TraceRoute.ofMap Γ Γ (fun a => some a)).fiber x).map _ = _
  exact congrArg (List.map _) (TraceRoute.fiber_identity Γ x)

theorem predecessors_conjL_right (Γ Θ Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P (Γ ++ A :: B :: Θ) Δ) {C : NormalForm P} (x : At Δ C) :
    (conjL Γ Θ Δ A B f).predecessors .right x =
      [⟨⟨_,_,f,Premise.conjL Γ Θ Δ A B f⟩,x⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change ((TraceRoute.ofMap Δ Δ (fun a => some a)).fiber x).map _ = _
  exact congrArg (List.map _) (TraceRoute.fiber_identity Δ x)

/-- Opposite-side unary logic retains the exact selected position. -/
theorem rho_disjR_left (Γ Δ Λ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ (Δ ++ A :: B :: Λ)) {C : NormalForm P} (x : At Γ C) :
    (disjR Γ Δ Λ A B f).rho .left x = 1 + f.rho .left x := by
  have hs := congrArg (fun us : List (Upper (disjR Γ Δ Λ A B f) .left C) =>
    1 + (us.map (fun a => a.branch.proof.rho .left a.position)).sum)
    (predecessors_disjR_left Γ Δ Λ A B f x)
  exact ((disjR Γ Δ Λ A B f).rho_eq .left x).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using hs)

theorem rho_conjL_right (Γ Θ Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P (Γ ++ A :: B :: Θ) Δ) {C : NormalForm P} (x : At Δ C) :
    (conjL Γ Θ Δ A B f).rho .right x = 1 + f.rho .right x := by
  have hs := congrArg (fun us : List (Upper (conjL Γ Θ Δ A B f) .right C) =>
    1 + (us.map (fun a => a.branch.proof.rho .right a.position)).sum)
    (predecessors_conjL_right Γ Θ Δ A B f x)
  exact ((conjL Γ Θ Δ A B f).rho_eq .right x).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using hs)

theorem disjR_principal_leaf (Γ Δ Λ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ (Δ ++ A :: B :: Λ)) :
    (disjR Γ Δ Λ A B f).Leaf .right (At.shift Δ (.here (.disj A B) Λ)) := by
  have hi : (At.shift Δ (.here (.disj A B) Λ)).index = Δ.length :=
    (At.index_shift Δ (.here (.disj A B) Λ)).trans (Nat.add_zero _)
  change (if (At.shift Δ (.here (.disj A B) Λ)).index = Δ.length then 0 else 1) = 0
  rw [ite_eq_left hi]

theorem conjL_principal_leaf (Γ Θ Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P (Γ ++ A :: B :: Θ) Δ) :
    (conjL Γ Θ Δ A B f).Leaf .left (At.shift Γ (.here (.conj A B) Θ)) := by
  have hi : (At.shift Γ (.here (.conj A B) Θ)).index = Γ.length :=
    (At.index_shift Γ (.here (.conj A B) Θ)).trans (Nat.add_zero _)
  change (if (At.shift Γ (.here (.conj A B) Θ)).index = Γ.length then 0 else 1) = 0
  rw [ite_eq_left hi]

/-- Whole-formula tracing stops at the introduced formula, not at its components. -/
theorem disjR_principal_predecessors (Γ Δ Λ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ (Δ ++ A :: B :: Λ)) :
    (disjR Γ Δ Λ A B f).predecessors .right (At.shift Δ (.here (.disj A B) Λ)) = [] :=
  List.length_eq_zero_iff.mp
    (((disjR Γ Δ Λ A B f).sourceArity_correct .right _).trans (disjR_principal_leaf ..))

theorem conjL_principal_predecessors (Γ Θ Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P (Γ ++ A :: B :: Θ) Δ) :
    (conjL Γ Θ Δ A B f).predecessors .left (At.shift Γ (.here (.conj A B) Θ)) = [] :=
  List.length_eq_zero_iff.mp
    (((conjL Γ Θ Δ A B f).sourceArity_correct .left _).trans (conjL_principal_leaf ..))

theorem rho_disjR_principal (Γ Δ Λ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ (Δ ++ A :: B :: Λ)) :
    (disjR Γ Δ Λ A B f).rho .right (At.shift Δ (.here (.disj A B) Λ)) = 1 :=
  (disjR Γ Δ Λ A B f).rho_leaf .right _ (disjR_principal_leaf ..)

theorem rho_conjL_principal (Γ Θ Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P (Γ ++ A :: B :: Θ) Δ) :
    (conjL Γ Θ Δ A B f).rho .left (At.shift Γ (.here (.conj A B) Θ)) = 1 :=
  (conjL Γ Θ Δ A B f).rho_leaf .left _ (conjL_principal_leaf ..)

end G
end DosenPetric.Reduced.Gentzen
