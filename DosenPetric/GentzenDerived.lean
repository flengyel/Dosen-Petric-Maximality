module

public import DosenPetric.PositiveGentzenSyntax

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Only equality of list indices is transported; formula isomorphisms stay explicit. -/
def termTransport {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (t : Term P (ante Γ) (succ Δ)) : Term P (ante Γ') (succ Δ') := hΓ ▸ hΔ ▸ t

namespace G

def reindex {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (g : G P Γ Δ) : G P Γ' Δ' := hΓ ▸ hΔ ▸ g

theorem denote_reindex {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (g : G P Γ Δ) : (reindex hΓ hΔ g).denote = termTransport hΓ hΔ g.denote := by
  cases hΓ; cases hΔ; rfl

theorem count_reindex {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (g : G P Γ Δ) : (reindex hΓ hΔ g).cutCount = g.cutCount := by
  cases hΓ; cases hΔ; rfl

/-- The source cut with both selected occurrences at arbitrary explicit gaps. -/
def cutAt {Γ₁ Γ₂ Γ₃ Δ₁ Δ₂ Δ₃ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ₃ (Δ₂ ++ [C] ++ Δ₁)) (g : G P (Γ₁ ++ [C] ++ Γ₂) Δ₃) :
    G P ((Γ₁ ++ Γ₂) ++ Γ₃) (Δ₃ ++ (Δ₂ ++ Δ₁)) := by
  have f' : G P Γ₃ (C :: (Δ₂ ++ Δ₁)) := .exchangeR Γ₃ [] Δ₂ [C] Δ₁ f
  have g' : G P (C :: (Γ₁ ++ Γ₂)) Δ₃ := .exchangeL [] Γ₁ [C] Γ₂ Δ₃ g
  exact G.cut f' g'

theorem cutAt_count {Γ₁ Γ₂ Γ₃ Δ₁ Δ₂ Δ₃ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ₃ (Δ₂ ++ [C] ++ Δ₁)) (g : G P (Γ₁ ++ [C] ++ Γ₂) Δ₃) :
    (cutAt f g).cutCount = f.cutCount + g.cutCount + 1 := by
  simp only [cutAt, cutCount]

theorem cutAt_denote {Γ₁ Γ₂ Γ₃ Δ₁ Δ₂ Δ₃ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ₃ (Δ₂ ++ [C] ++ Δ₁)) (g : G P (Γ₁ ++ [C] ++ Γ₂) Δ₃) :
    (cutAt f g).denote = Rules.cut
      (.comp f.denote (exchange .disj [] Δ₂ [C] Δ₁).toTerm)
      (.comp (exchange .conj [] Γ₁ [C] Γ₂).invTerm g.denote) := rfl

theorem contraction_middle (Δ Λ : List (NormalForm P)) (C : NormalForm P)
    (gs : List (List (NormalForm P))) :
    gaps (Δ :: gs) ++ C :: Λ = Δ ++ gaps gs ++ [C] ++ Λ := by
  simp only [gaps, List.append_assoc, List.singleton_append]

theorem contraction_first (Δ Λ : List (NormalForm P)) (C : NormalForm P)
    (gs : List (List (NormalForm P))) :
    Δ ++ [C] ++ gaps gs ++ Λ = Δ ++ C :: (gaps gs ++ Λ) := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Source right contraction retains its first selected copy, after exchange. -/
def contractRFirst (Γ Δ Λ : List (NormalForm P)) (C : NormalForm P)
    (gs : List (List (NormalForm P))) (hn : 1 ≤ gs.length)
    (f : G P Γ (repeated C (Δ :: gs) ++ Λ)) : G P Γ (Δ ++ C :: (gaps gs ++ Λ)) :=
  reindex rfl (contraction_first Δ Λ C gs)
    (.exchangeR Γ Δ (gaps gs) [C] Λ
      (reindex rfl (contraction_middle Δ Λ C gs)
        (.contractR Γ C (Δ :: gs) Λ (Nat.succ_le_succ hn) f)))

theorem contractRFirst_denote (Γ Δ Λ : List (NormalForm P)) (C : NormalForm P)
    (gs : List (List (NormalForm P))) (hn : 1 ≤ gs.length)
    (f : G P Γ (repeated C (Δ :: gs) ++ Λ)) :
    (contractRFirst Γ Δ Λ C gs hn f).denote =
      termTransport rfl (contraction_first Δ Λ C gs)
        (.comp (termTransport rfl (contraction_middle Δ Λ C gs)
          (.comp f.denote (copies C (Δ :: gs) Λ).coproduct))
            (exchange .disj Δ (gaps gs) [C] Λ).toTerm) := by
  rw [contractRFirst, denote_reindex]
  simp only [denote, denote_reindex]

theorem contractRFirst_count (Γ Δ Λ : List (NormalForm P)) (C : NormalForm P)
    (gs : List (List (NormalForm P))) (hn : 1 ≤ gs.length)
    (f : G P Γ (repeated C (Δ :: gs) ++ Λ)) :
    (contractRFirst Γ Δ Λ C gs hn f).cutCount = f.cutCount := by
  simp only [contractRFirst, count_reindex, cutCount]

/-- The source rightmost left-thinning operation, with its list transport. -/
def thinLast {Γ Δ : List (NormalForm P)} (A : NormalForm P) (f : G P Γ Δ) :
    G P (Γ ++ [A]) Δ := .thinL Γ [] Δ A (reindex (List.append_nil Γ).symm rfl f)

theorem thinLast_denote {Γ Δ : List (NormalForm P)} (A : NormalForm P) (f : G P Γ Δ) :
    (thinLast A f).denote = .comp (Route.thin Γ [] A).product
      (termTransport (List.append_nil Γ).symm rfl f.denote) := by
  simp only [thinLast, denote, denote_reindex]

end G
end DosenPetric.Reduced.Gentzen
