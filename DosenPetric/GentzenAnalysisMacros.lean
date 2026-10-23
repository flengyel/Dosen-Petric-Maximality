module

public import DosenPetric.GentzenProofInterfaces

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.G
universe u
variable {P : Type u}

theorem atomized_reindex {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (g : G P Γ Δ) : (g.reindex hΓ hΔ).Atomized ↔ g.Atomized := by
  cases hΓ; cases hΔ; rfl

theorem cutFree_reindex {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (g : G P Γ Δ) : (g.reindex hΓ hΔ).CutFree ↔ g.CutFree := by
  rw [CutFree, count_reindex]; rfl

theorem atomized_exchangeL (Γ X Y Θ Δ : List (NormalForm P))
    (g : G P (Γ ++ X ++ Y ++ Θ) Δ) :
    (G.exchangeL Γ X Y Θ Δ g).Atomized ↔ g.Atomized := Iff.rfl

theorem atomized_exchangeR (Γ Δ X Y Λ : List (NormalForm P))
    (g : G P Γ (Δ ++ X ++ Y ++ Λ)) :
    (G.exchangeR Γ Δ X Y Λ g).Atomized ↔ g.Atomized := Iff.rfl

theorem cutFree_exchangeL (Γ X Y Θ Δ : List (NormalForm P))
    (g : G P (Γ ++ X ++ Y ++ Θ) Δ) :
    (G.exchangeL Γ X Y Θ Δ g).CutFree ↔ g.CutFree := Iff.rfl

theorem cutFree_exchangeR (Γ Δ X Y Λ : List (NormalForm P))
    (g : G P Γ (Δ ++ X ++ Y ++ Λ)) :
    (G.exchangeR Γ Δ X Y Λ g).CutFree ↔ g.CutFree := Iff.rfl

theorem atomized_contractL (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Δ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (g : G P (repeated C gs ++ Θ) Δ) :
    (G.contractL C gs Θ Δ hn g).Atomized ↔ g.Atomized := Iff.rfl

theorem atomized_contractR (Γ : List (NormalForm P)) (C : NormalForm P)
    (gs : List (List (NormalForm P))) (Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (g : G P Γ (repeated C gs ++ Λ)) :
    (G.contractR Γ C gs Λ hn g).Atomized ↔ g.Atomized := Iff.rfl

theorem cutFree_contractL (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Δ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (g : G P (repeated C gs ++ Θ) Δ) :
    (G.contractL C gs Θ Δ hn g).CutFree ↔ g.CutFree := Iff.rfl

theorem cutFree_contractR (Γ : List (NormalForm P)) (C : NormalForm P)
    (gs : List (List (NormalForm P))) (Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (g : G P Γ (repeated C gs ++ Λ)) :
    (G.contractR Γ C gs Λ hn g).CutFree ↔ g.CutFree := Iff.rfl

theorem atomized_contractRFirst (Γ Δ Λ : List (NormalForm P)) (C : NormalForm P)
    (gs : List (List (NormalForm P))) (hn : 1 ≤ gs.length)
    (g : G P Γ (repeated C (Δ :: gs) ++ Λ)) :
    (contractRFirst Γ Δ Λ C gs hn g).Atomized ↔ g.Atomized := by
  simp only [contractRFirst, atomized_reindex, Atomized]

theorem cutFree_contractRFirst (Γ Δ Λ : List (NormalForm P)) (C : NormalForm P)
    (gs : List (List (NormalForm P))) (hn : 1 ≤ gs.length)
    (g : G P Γ (repeated C (Δ :: gs) ++ Λ)) :
    (contractRFirst Γ Δ Λ C gs hn g).CutFree ↔ g.CutFree := by
  rw [CutFree, contractRFirst_count]; rfl

theorem atomized_thinLast {Γ Δ : List (NormalForm P)} (A : NormalForm P) (g : G P Γ Δ) :
    (thinLast A g).Atomized ↔ AtomicFormula A ∧ g.Atomized := by
  simp only [thinLast, Atomized, atomized_reindex]

theorem cutFree_thinLast {Γ Δ : List (NormalForm P)} (A : NormalForm P) (g : G P Γ Δ) :
    (thinLast A g).CutFree ↔ g.CutFree := by
  simp only [thinLast, CutFree, cutCount, count_reindex]

end DosenPetric.Reduced.Gentzen.G
