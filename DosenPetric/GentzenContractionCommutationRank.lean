module

public import DosenPetric.GentzenContractionCommutation

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W1.Contraction
universe u
variable {P : Type u}
variable (C D : NormalForm P) (gs hs : List (List (NormalForm P)))
  (Θ Λ : List (NormalForm P)) (hn : 2 ≤ gs.length) (hm : 2 ≤ hs.length)
  (f : G P (repeated C gs ++ Θ) (repeated D hs ++ Λ))

theorem outerL_left :
    (outerL C D gs hs Θ Λ hn hm f).rho .left (At.shift (gaps gs) (.here C Θ)) =
      leftRank C D gs hs Θ Λ hn f + gs.length := by
  change G.contractionRankL C gs Θ (gaps hs ++ D :: Λ) hn (innerR C D gs hs Θ Λ hm f) =
    G.contractionRankL C gs Θ (repeated D hs ++ Λ) hn f + gs.length
  rw [G.contractionRankL_eq,G.contractionRankL_eq]
  have he : (selectedCopies C gs Θ).map
      (fun (x : At (repeated C gs ++ Θ) C) => (innerR C D gs hs Θ Λ hm f).rho .left x) =
      (selectedCopies C gs Θ).map (fun (x : At (repeated C gs ++ Θ) C) => 1 + f.rho .left x) := by
    apply List.map_congr_left
    intro x _
    exact G.rho_contractR_left _ D hs Λ hm f x
  rw [he]
  have hs₁ := G.sum_map_one_add (selectedCopies C gs Θ)
    (fun (x : At (repeated C gs ++ Θ) C) => f.rho .left x)
  have hl := selectedCopies_length C gs Θ
  omega

theorem outerR_left :
    (outerR C D gs hs Θ Λ hn hm f).rho .left (At.shift (gaps gs) (.here C Θ)) =
      leftRank C D gs hs Θ Λ hn f + 1 :=
  (G.rho_contractR_left _ D hs Λ hm (innerL C D gs hs Θ Λ hn f)
    (At.shift (gaps gs) (.here C Θ))).trans (Nat.add_comm _ _)

theorem outerL_right :
    (outerL C D gs hs Θ Λ hn hm f).rho .right (At.shift (gaps hs) (.here D Λ)) =
      rightRank C D gs hs Θ Λ hm f + 1 :=
  (G.rho_contractL_right C gs Θ _ hn (innerR C D gs hs Θ Λ hm f)
    (At.shift (gaps hs) (.here D Λ))).trans (Nat.add_comm _ _)

theorem outerR_right :
    (outerR C D gs hs Θ Λ hn hm f).rho .right (At.shift (gaps hs) (.here D Λ)) =
      rightRank C D gs hs Θ Λ hm f + hs.length := by
  change G.contractionRankR (gaps gs ++ C :: Θ) D hs Λ hm (innerL C D gs hs Θ Λ hn f) =
    G.contractionRankR (repeated C gs ++ Θ) D hs Λ hm f + hs.length
  rw [G.contractionRankR_eq,G.contractionRankR_eq]
  have he : (selectedCopies D hs Λ).map
      (fun (y : At (repeated D hs ++ Λ) D) => (innerL C D gs hs Θ Λ hn f).rho .right y) =
      (selectedCopies D hs Λ).map (fun (y : At (repeated D hs ++ Λ) D) => 1 + f.rho .right y) := by
    apply List.map_congr_left
    intro y _
    exact G.rho_contractL_right C gs Θ _ hn f y
  rw [he]
  have hs₁ := G.sum_map_one_add (selectedCopies D hs Λ)
    (fun (y : At (repeated D hs ++ Λ) D) => f.rho .right y)
  have hl := selectedCopies_length D hs Λ
  omega

theorem innerL_rank_lt_outerL : leftRank C D gs hs Θ Λ hn f <
    (outerL C D gs hs Θ Λ hn hm f).rho .left (At.shift (gaps gs) (.here C Θ)) := by
  have h := outerL_left C D gs hs Θ Λ hn hm f
  omega

theorem innerR_rank_lt_outerR : rightRank C D gs hs Θ Λ hm f <
    (outerR C D gs hs Θ Λ hn hm f).rho .right (At.shift (gaps hs) (.here D Λ)) := by
  have h := outerR_right C D gs hs Θ Λ hn hm f
  omega

/-- Left-directed reduction outerL to outerR; the left endpoint loses n-1. -/
theorem left_directed_balance :
    (outerL C D gs hs Θ Λ hn hm f).rho .left (At.shift (gaps gs) (.here C Θ)) + 1 =
      (outerR C D gs hs Θ Λ hn hm f).rho .left (At.shift (gaps gs) (.here C Θ)) + gs.length := by
  have h₁ := outerL_left C D gs hs Θ Λ hn hm f
  have h₂ := outerR_left C D gs hs Θ Λ hn hm f
  omega

/-- Right-directed reduction outerR to outerL; the right endpoint loses m-1. -/
theorem right_directed_balance :
    (outerR C D gs hs Θ Λ hn hm f).rho .right (At.shift (gaps hs) (.here D Λ)) + 1 =
      (outerL C D gs hs Θ Λ hn hm f).rho .right (At.shift (gaps hs) (.here D Λ)) + hs.length := by
  have h₁ := outerR_right C D gs hs Θ Λ hn hm f
  have h₂ := outerL_right C D gs hs Θ Λ hn hm f
  omega

theorem left_directed_decrease :
    (outerR C D gs hs Θ Λ hn hm f).rho .left (At.shift (gaps gs) (.here C Θ)) <
      (outerL C D gs hs Θ Λ hn hm f).rho .left (At.shift (gaps gs) (.here C Θ)) := by
  have h := left_directed_balance C D gs hs Θ Λ hn hm f
  omega

theorem right_directed_decrease :
    (outerL C D gs hs Θ Λ hn hm f).rho .right (At.shift (gaps hs) (.here D Λ)) <
      (outerR C D gs hs Θ Λ hn hm f).rho .right (At.shift (gaps hs) (.here D Λ)) := by
  have h := right_directed_balance C D gs hs Θ Λ hn hm f
  omega

/-- The left-directed move increases the other displayed endpoint rank. -/
theorem left_directed_right_increase :
    (outerL C D gs hs Θ Λ hn hm f).rho .right (At.shift (gaps hs) (.here D Λ)) <
      (outerR C D gs hs Θ Λ hn hm f).rho .right (At.shift (gaps hs) (.here D Λ)) :=
  right_directed_decrease C D gs hs Θ Λ hn hm f

theorem right_directed_left_increase :
    (outerR C D gs hs Θ Λ hn hm f).rho .left (At.shift (gaps gs) (.here C Θ)) <
      (outerL C D gs hs Θ Λ hn hm f).rho .left (At.shift (gaps gs) (.here C Θ)) :=
  left_directed_decrease C D gs hs Θ Λ hn hm f

theorem endpointSum_balance :
    endpointSum C D gs hs Θ Λ (outerL C D gs hs Θ Λ hn hm f) + hs.length =
      endpointSum C D gs hs Θ Λ (outerR C D gs hs Θ Λ hn hm f) + gs.length := by
  have h₁ := left_directed_balance C D gs hs Θ Λ hn hm f
  have h₂ := right_directed_balance C D gs hs Θ Λ hn hm f
  unfold endpointSum
  omega

theorem endpointSum_eq_of_lengths_eq (h : gs.length = hs.length) :
    endpointSum C D gs hs Θ Λ (outerL C D gs hs Θ Λ hn hm f) =
      endpointSum C D gs hs Θ Λ (outerR C D gs hs Θ Λ hn hm f) := by
  have he := endpointSum_balance C D gs hs Θ Λ hn hm f
  omega

end DosenPetric.Reduced.Gentzen.W1.Contraction
