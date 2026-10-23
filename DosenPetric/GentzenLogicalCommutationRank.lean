module

public import DosenPetric.GentzenLogicalCommutation

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace W1.Logical

section Left
variable (A B C : NormalForm P) (gs : List (List (NormalForm P)))
  (Θ Δ Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
  (f : G P (repeated C gs ++ Θ) (Δ ++ A :: B :: Λ))

/-- Every selected upper copy loses its own opposite-side unary logical node. -/
theorem contraction_lossL :
    G.contractionRankL C gs Θ (Δ ++ .disj A B :: Λ) hn (G.disjR _ Δ Λ A B f) =
      G.contractionRankL C gs Θ (Δ ++ A :: B :: Λ) hn f + gs.length := by
  rw [G.contractionRankL_eq,G.contractionRankL_eq]
  have hm : (selectedCopies C gs Θ).map
      (fun (x : At (repeated C gs ++ Θ) C) => (G.disjR _ Δ Λ A B f).rho .left x) =
      (selectedCopies C gs Θ).map (fun (x : At (repeated C gs ++ Θ) C) => 1 + f.rho .left x) := by
    apply List.map_congr_left
    intro x _
    exact G.rho_disjR_left _ Δ Λ A B f x
  rw [hm]
  have hs := G.sum_map_one_add (selectedCopies C gs Θ)
    (fun (x : At (repeated C gs ++ Θ) C) => f.rho .left x)
  have hl := selectedCopies_length C gs Θ
  omega

theorem endpoint_rankL :
    (newL A B C gs Θ Δ Λ hn f).rho .left (At.shift (gaps gs) (.here C Θ)) =
      G.contractionRankL C gs Θ (Δ ++ A :: B :: Λ) hn f + 1 := by
  exact (G.rho_disjR_left _ Δ Λ A B (innerL A B C gs Θ Δ Λ hn f)
    (At.shift (gaps gs) (.here C Θ))).trans (Nat.add_comm _ _)

theorem contraction_decreasesL :
    G.contractionRankL C gs Θ (Δ ++ A :: B :: Λ) hn f <
      G.contractionRankL C gs Θ (Δ ++ .disj A B :: Λ) hn (G.disjR _ Δ Λ A B f) := by
  have h := contraction_lossL A B C gs Θ Δ Λ hn f
  omega

/-- Subtraction-free statement of the whole selected-position loss n-1. -/
theorem endpoint_lossL :
    (oldL A B C gs Θ Δ Λ hn f).rho .left (At.shift (gaps gs) (.here C Θ)) + 1 =
      (newL A B C gs Θ Δ Λ hn f).rho .left (At.shift (gaps gs) (.here C Θ)) + gs.length := by
  have h := contraction_lossL A B C gs Θ Δ Λ hn f
  have he := endpoint_rankL A B C gs Θ Δ Λ hn f
  change (oldL A B C gs Θ Δ Λ hn f).rho .left (At.shift (gaps gs) (.here C Θ)) = _ at h
  omega

theorem endpoint_decreasesL :
    (newL A B C gs Θ Δ Λ hn f).rho .left (At.shift (gaps gs) (.here C Θ)) <
      (oldL A B C gs Θ Δ Λ hn f).rho .left (At.shift (gaps gs) (.here C Θ)) := by
  have h := endpoint_lossL A B C gs Θ Δ Λ hn f
  omega

theorem newL_principal_predecessors :
    (newL A B C gs Θ Δ Λ hn f).predecessors .right (At.shift Δ (.here (.disj A B) Λ)) = [] :=
  G.disjR_principal_predecessors _ Δ Λ A B (innerL A B C gs Θ Δ Λ hn f)

theorem newL_principal_rank :
    (newL A B C gs Θ Δ Λ hn f).rho .right (At.shift Δ (.here (.disj A B) Λ)) = 1 :=
  G.rho_disjR_principal _ Δ Λ A B (innerL A B C gs Θ Δ Λ hn f)

theorem oldL_principal_rank :
    (oldL A B C gs Θ Δ Λ hn f).rho .right (At.shift Δ (.here (.disj A B) Λ)) = 2 := by
  have h := G.rho_contractL_right C gs Θ _ hn (G.disjR _ Δ Λ A B f)
    (At.shift Δ (.here (.disj A B) Λ))
  exact h.trans (congrArg (fun n => 1 + n) (G.rho_disjR_principal _ Δ Λ A B f))

end Left

section Right
variable (A B C : NormalForm P) (gs : List (List (NormalForm P)))
  (Γ Θ Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
  (f : G P (Γ ++ A :: B :: Θ) (repeated C gs ++ Λ))

theorem contraction_lossR :
    G.contractionRankR (Γ ++ .conj A B :: Θ) C gs Λ hn (G.conjL Γ Θ _ A B f) =
      G.contractionRankR (Γ ++ A :: B :: Θ) C gs Λ hn f + gs.length := by
  rw [G.contractionRankR_eq,G.contractionRankR_eq]
  have hm : (selectedCopies C gs Λ).map
      (fun (x : At (repeated C gs ++ Λ) C) => (G.conjL Γ Θ _ A B f).rho .right x) =
      (selectedCopies C gs Λ).map (fun (x : At (repeated C gs ++ Λ) C) => 1 + f.rho .right x) := by
    apply List.map_congr_left
    intro x _
    exact G.rho_conjL_right Γ Θ _ A B f x
  rw [hm]
  have hs := G.sum_map_one_add (selectedCopies C gs Λ)
    (fun (x : At (repeated C gs ++ Λ) C) => f.rho .right x)
  have hl := selectedCopies_length C gs Λ
  omega

theorem endpoint_rankR :
    (newR A B C gs Γ Θ Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ)) =
      G.contractionRankR (Γ ++ A :: B :: Θ) C gs Λ hn f + 1 := by
  exact (G.rho_conjL_right Γ Θ _ A B (innerR A B C gs Γ Θ Λ hn f)
    (At.shift (gaps gs) (.here C Λ))).trans (Nat.add_comm _ _)

theorem contraction_decreasesR :
    G.contractionRankR (Γ ++ A :: B :: Θ) C gs Λ hn f <
      G.contractionRankR (Γ ++ .conj A B :: Θ) C gs Λ hn (G.conjL Γ Θ _ A B f) := by
  have h := contraction_lossR A B C gs Γ Θ Λ hn f
  omega

theorem endpoint_lossR :
    (oldR A B C gs Γ Θ Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ)) + 1 =
      (newR A B C gs Γ Θ Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ)) + gs.length := by
  have h := contraction_lossR A B C gs Γ Θ Λ hn f
  have he := endpoint_rankR A B C gs Γ Θ Λ hn f
  change (oldR A B C gs Γ Θ Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ)) = _ at h
  omega

theorem endpoint_decreasesR :
    (newR A B C gs Γ Θ Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ)) <
      (oldR A B C gs Γ Θ Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ)) := by
  have h := endpoint_lossR A B C gs Γ Θ Λ hn f
  omega

theorem newR_principal_predecessors :
    (newR A B C gs Γ Θ Λ hn f).predecessors .left (At.shift Γ (.here (.conj A B) Θ)) = [] :=
  G.conjL_principal_predecessors Γ Θ _ A B (innerR A B C gs Γ Θ Λ hn f)

theorem newR_principal_rank :
    (newR A B C gs Γ Θ Λ hn f).rho .left (At.shift Γ (.here (.conj A B) Θ)) = 1 :=
  G.rho_conjL_principal Γ Θ _ A B (innerR A B C gs Γ Θ Λ hn f)

theorem oldR_principal_rank :
    (oldR A B C gs Γ Θ Λ hn f).rho .left (At.shift Γ (.here (.conj A B) Θ)) = 2 := by
  have h := G.rho_contractR_left _ C gs Λ hn (G.conjL Γ Θ _ A B f)
    (At.shift Γ (.here (.conj A B) Θ))
  exact h.trans (congrArg (fun n => 1 + n) (G.rho_conjL_principal Γ Θ _ A B f))

end Right
end W1.Logical
end DosenPetric.Reduced.Gentzen
