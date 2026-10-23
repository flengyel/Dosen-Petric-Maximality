module

public import DosenPetric.GentzenExchangeCommutation

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace W1.Exchange

section Left
variable (C : NormalForm P) (gs : List (List (NormalForm P)))
  (Θ Δ X Y Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
  (f : G P (repeated C gs ++ Θ) (Δ ++ X ++ Y ++ Λ))

/-- Every selected upper copy loses its own opposite-side exchange node. -/
theorem contraction_lossL :
    G.contractionRankL C gs Θ (Δ ++ Y ++ X ++ Λ) hn (G.exchangeR _ Δ X Y Λ f) =
      G.contractionRankL C gs Θ (Δ ++ X ++ Y ++ Λ) hn f + gs.length := by
  rw [G.contractionRankL_eq,G.contractionRankL_eq]
  have hm : (selectedCopies C gs Θ).map
      (fun (x : At (repeated C gs ++ Θ) C) => (G.exchangeR _ Δ X Y Λ f).rho .left x) =
      (selectedCopies C gs Θ).map (fun (x : At (repeated C gs ++ Θ) C) => 1 + f.rho .left x) := by
    apply List.map_congr_left
    intro x _
    exact G.rho_exchangeR_left _ Δ X Y Λ f x
  rw [hm]
  have hs := G.sum_map_one_add (selectedCopies C gs Θ)
    (fun (x : At (repeated C gs ++ Θ) C) => f.rho .left x)
  have hl := selectedCopies_length C gs Θ
  omega

theorem endpoint_rankL :
    (newL C gs Θ Δ X Y Λ hn f).rho .left (At.shift (gaps gs) (.here C Θ)) =
      G.contractionRankL C gs Θ (Δ ++ X ++ Y ++ Λ) hn f + 1 := by
  exact (G.rho_exchangeR_left _ Δ X Y Λ (innerL C gs Θ Δ X Y Λ hn f)
    (At.shift (gaps gs) (.here C Θ))).trans (Nat.add_comm _ _)

theorem contraction_decreasesL :
    G.contractionRankL C gs Θ (Δ ++ X ++ Y ++ Λ) hn f <
      G.contractionRankL C gs Θ (Δ ++ Y ++ X ++ Λ) hn (G.exchangeR _ Δ X Y Λ f) := by
  have h := contraction_lossL C gs Θ Δ X Y Λ hn f
  omega

/-- Subtraction-free statement of the whole selected-position loss n-1. -/
theorem endpoint_lossL :
    (oldL C gs Θ Δ X Y Λ hn f).rho .left (At.shift (gaps gs) (.here C Θ)) + 1 =
      (newL C gs Θ Δ X Y Λ hn f).rho .left (At.shift (gaps gs) (.here C Θ)) + gs.length := by
  have h := contraction_lossL C gs Θ Δ X Y Λ hn f
  have he := endpoint_rankL C gs Θ Δ X Y Λ hn f
  change (oldL C gs Θ Δ X Y Λ hn f).rho .left (At.shift (gaps gs) (.here C Θ)) = _ at h
  omega

theorem endpoint_decreasesL :
    (newL C gs Θ Δ X Y Λ hn f).rho .left (At.shift (gaps gs) (.here C Θ)) <
      (oldL C gs Θ Δ X Y Λ hn f).rho .left (At.shift (gaps gs) (.here C Θ)) := by
  have h := endpoint_lossL C gs Θ Δ X Y Λ hn f
  omega

end Left

section Right
variable (C : NormalForm P) (gs : List (List (NormalForm P)))
  (Γ X Y Θ Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
  (f : G P (Γ ++ X ++ Y ++ Θ) (repeated C gs ++ Λ))

theorem contraction_lossR :
    G.contractionRankR (Γ ++ Y ++ X ++ Θ) C gs Λ hn (G.exchangeL Γ X Y Θ _ f) =
      G.contractionRankR (Γ ++ X ++ Y ++ Θ) C gs Λ hn f + gs.length := by
  rw [G.contractionRankR_eq,G.contractionRankR_eq]
  have hm : (selectedCopies C gs Λ).map
      (fun (x : At (repeated C gs ++ Λ) C) => (G.exchangeL Γ X Y Θ _ f).rho .right x) =
      (selectedCopies C gs Λ).map (fun (x : At (repeated C gs ++ Λ) C) => 1 + f.rho .right x) := by
    apply List.map_congr_left
    intro x _
    exact G.rho_exchangeL_right Γ X Y Θ _ f x
  rw [hm]
  have hs := G.sum_map_one_add (selectedCopies C gs Λ)
    (fun (x : At (repeated C gs ++ Λ) C) => f.rho .right x)
  have hl := selectedCopies_length C gs Λ
  omega

theorem endpoint_rankR :
    (newR C gs Γ X Y Θ Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ)) =
      G.contractionRankR (Γ ++ X ++ Y ++ Θ) C gs Λ hn f + 1 := by
  exact (G.rho_exchangeL_right Γ X Y Θ _ (innerR C gs Γ X Y Θ Λ hn f)
    (At.shift (gaps gs) (.here C Λ))).trans (Nat.add_comm _ _)

theorem contraction_decreasesR :
    G.contractionRankR (Γ ++ X ++ Y ++ Θ) C gs Λ hn f <
      G.contractionRankR (Γ ++ Y ++ X ++ Θ) C gs Λ hn (G.exchangeL Γ X Y Θ _ f) := by
  have h := contraction_lossR C gs Γ X Y Θ Λ hn f
  omega

theorem endpoint_lossR :
    (oldR C gs Γ X Y Θ Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ)) + 1 =
      (newR C gs Γ X Y Θ Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ)) + gs.length := by
  have h := contraction_lossR C gs Γ X Y Θ Λ hn f
  have he := endpoint_rankR C gs Γ X Y Θ Λ hn f
  change (oldR C gs Γ X Y Θ Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ)) = _ at h
  omega

theorem endpoint_decreasesR :
    (newR C gs Γ X Y Θ Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ)) <
      (oldR C gs Γ X Y Θ Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ)) := by
  have h := endpoint_lossR C gs Γ X Y Θ Λ hn f
  omega

end Right
end W1.Exchange
end DosenPetric.Reduced.Gentzen
