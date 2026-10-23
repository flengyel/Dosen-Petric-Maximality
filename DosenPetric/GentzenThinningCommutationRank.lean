module

public import DosenPetric.GentzenThinningCommutation

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace W1

section Left
variable (C D : NormalForm P) (gs : List (List (NormalForm P)))
  (Θ Δ Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
  (f : G P (repeated C gs ++ Θ) (Δ ++ Λ))

/-- Every selected upper copy loses its own opposite-side thinning node. -/
theorem contraction_lossL :
    G.contractionRankL C gs Θ (Δ ++ D :: Λ) hn (G.thinR _ Δ Λ D f) =
      G.contractionRankL C gs Θ (Δ ++ Λ) hn f + gs.length := by
  rw [G.contractionRankL_eq,G.contractionRankL_eq]
  have hm : (selectedCopies C gs Θ).map
      (fun (x : At (repeated C gs ++ Θ) C) => (G.thinR _ Δ Λ D f).rho .left x) =
      (selectedCopies C gs Θ).map (fun (x : At (repeated C gs ++ Θ) C) => 1 + f.rho .left x) := by
    apply List.map_congr_left
    intro x _
    exact G.rho_thinR_left _ Δ Λ D f x
  rw [hm]
  have hs := G.sum_map_one_add (selectedCopies C gs Θ)
    (fun (x : At (repeated C gs ++ Θ) C) => f.rho .left x)
  have hl := selectedCopies_length C gs Θ
  omega

theorem endpoint_rankL :
    (newL C D gs Θ Δ Λ hn f).rho .left (At.shift (gaps gs) (.here C Θ)) =
      G.contractionRankL C gs Θ (Δ ++ Λ) hn f + 1 := by
  exact (G.rho_thinR_left _ Δ Λ D (innerL C gs Θ Δ Λ hn f)
    (At.shift (gaps gs) (.here C Θ))).trans (Nat.add_comm _ _)

theorem contraction_decreasesL :
    G.contractionRankL C gs Θ (Δ ++ Λ) hn f <
      G.contractionRankL C gs Θ (Δ ++ D :: Λ) hn (G.thinR _ Δ Λ D f) := by
  have h := contraction_lossL C D gs Θ Δ Λ hn f
  omega

/-- Subtraction-free statement of the whole selected-position loss n-1. -/
theorem endpoint_lossL :
    (oldL C D gs Θ Δ Λ hn f).rho .left (At.shift (gaps gs) (.here C Θ)) + 1 =
      (newL C D gs Θ Δ Λ hn f).rho .left (At.shift (gaps gs) (.here C Θ)) + gs.length := by
  have h := contraction_lossL C D gs Θ Δ Λ hn f
  have he := endpoint_rankL C D gs Θ Δ Λ hn f
  change (oldL C D gs Θ Δ Λ hn f).rho .left (At.shift (gaps gs) (.here C Θ)) = _ at h
  omega

theorem endpoint_decreasesL :
    (newL C D gs Θ Δ Λ hn f).rho .left (At.shift (gaps gs) (.here C Θ)) <
      (oldL C D gs Θ Δ Λ hn f).rho .left (At.shift (gaps gs) (.here C Θ)) := by
  have h := endpoint_lossL C D gs Θ Δ Λ hn f
  omega

end Left

section Right
variable (C D : NormalForm P) (gs : List (List (NormalForm P)))
  (Γ Θ Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
  (f : G P (Γ ++ Θ) (repeated C gs ++ Λ))

theorem contraction_lossR :
    G.contractionRankR (Γ ++ D :: Θ) C gs Λ hn (G.thinL Γ Θ _ D f) =
      G.contractionRankR (Γ ++ Θ) C gs Λ hn f + gs.length := by
  rw [G.contractionRankR_eq,G.contractionRankR_eq]
  have hm : (selectedCopies C gs Λ).map
      (fun (x : At (repeated C gs ++ Λ) C) => (G.thinL Γ Θ _ D f).rho .right x) =
      (selectedCopies C gs Λ).map (fun (x : At (repeated C gs ++ Λ) C) => 1 + f.rho .right x) := by
    apply List.map_congr_left
    intro x _
    exact G.rho_thinL_right Γ Θ _ D f x
  rw [hm]
  have hs := G.sum_map_one_add (selectedCopies C gs Λ)
    (fun (x : At (repeated C gs ++ Λ) C) => f.rho .right x)
  have hl := selectedCopies_length C gs Λ
  omega

theorem endpoint_rankR :
    (newR C D gs Γ Θ Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ)) =
      G.contractionRankR (Γ ++ Θ) C gs Λ hn f + 1 := by
  exact (G.rho_thinL_right Γ Θ _ D (innerR C gs Γ Θ Λ hn f)
    (At.shift (gaps gs) (.here C Λ))).trans (Nat.add_comm _ _)

theorem contraction_decreasesR :
    G.contractionRankR (Γ ++ Θ) C gs Λ hn f <
      G.contractionRankR (Γ ++ D :: Θ) C gs Λ hn (G.thinL Γ Θ _ D f) := by
  have h := contraction_lossR C D gs Γ Θ Λ hn f
  omega

theorem endpoint_lossR :
    (oldR C D gs Γ Θ Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ)) + 1 =
      (newR C D gs Γ Θ Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ)) + gs.length := by
  have h := contraction_lossR C D gs Γ Θ Λ hn f
  have he := endpoint_rankR C D gs Γ Θ Λ hn f
  change (oldR C D gs Γ Θ Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ)) = _ at h
  omega

theorem endpoint_decreasesR :
    (newR C D gs Γ Θ Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ)) <
      (oldR C D gs Γ Θ Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ)) := by
  have h := endpoint_lossR C D gs Γ Θ Λ hn f
  omega

end Right
end W1
end DosenPetric.Reduced.Gentzen
