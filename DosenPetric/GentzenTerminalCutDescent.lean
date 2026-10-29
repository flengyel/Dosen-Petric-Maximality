module

public import DosenPetric.GentzenTerminalLogicalRanks
public import DosenPetric.GentzenSelectedContractionDescent

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace UnaryCast
/-- An input exchange preserves the selected output and descends to the actual
    premise, before any occurrence-routing adapter is introduced. -/
theorem exchangeL_left_cut_descent {F U Δ I J : List (NormalForm P)}
    (Γ X Y Θ : List (NormalForm P)) (hF : Γ++X++Y++Θ=F) (hU : Γ++Y++X++Θ=U)
    (f : G P F Δ) {C : NormalForm P} (a : At Δ C) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (exchangeL Γ X Y Θ hF hU Δ f) a h z) :
    PositionalCut.Clean f a h z ∧
      PositionalCut.rank f a h z < PositionalCut.rank (exchangeL Γ X Y Θ hF hU Δ f) a h z := by
  cases hU
  cases hF
  let b : Upper (G.exchangeL Γ X Y Θ Δ f) .right C :=
    ⟨⟨_,_,f,Premise.exchangeL Γ X Y Θ Δ f⟩,a⟩
  have hb : (G.exchangeL Γ X Y Θ Δ f).IsPredecessor .right a b := rfl
  exact ⟨PositionalCut.clean_left_predecessor hc b hb,
    PositionalCut.rank_left_predecessor _ _ h z b hb⟩
end UnaryCast

namespace BlockedSource
/-- The original first child is three inference steps above the terminal macro. -/
theorem disjLLast_left_first_descent {F U Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ) (a : At Δ C) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (disjLLast f g) (a.before Λ) h z) :
    PositionalCut.Clean f a h z ∧
      PositionalCut.rank f a h z < PositionalCut.rank (disjLLast f g) (a.before Λ) h z := by
  rw [disjLLast_eq] at hc ⊢
  have ht := UnaryCast.exchangeL_left_cut_descent [] [.disj A B] (F++U) [] _ _
    (G.disjL (headL A f) (headL B g)) (a.before Λ) h z hc
  have hm := PositionalCut.disjL_left_first_descent (headL A f) (headL B g) a h z ht.1
  have hf := UnaryCast.exchangeL_left_cut_descent [] F [A] [] _ _ f a h z hm.1
  exact ⟨hf.1,Nat.lt_trans hf.2 (Nat.lt_trans hm.2 ht.2)⟩

theorem disjLLast_left_second_descent {F U Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ) (a : At Λ C) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (disjLLast f g) (At.shift Δ a) h z) :
    PositionalCut.Clean g a h z ∧
      PositionalCut.rank g a h z < PositionalCut.rank (disjLLast f g) (At.shift Δ a) h z := by
  rw [disjLLast_eq] at hc ⊢
  have ht := UnaryCast.exchangeL_left_cut_descent [] [.disj A B] (F++U) [] _ _
    (G.disjL (headL A f) (headL B g)) (At.shift Δ a) h z hc
  have hm := PositionalCut.disjL_left_second_descent (headL A f) (headL B g) a h z ht.1
  have hg := UnaryCast.exchangeL_left_cut_descent [] U [B] [] _ _ g a h z hm.1
  exact ⟨hg.1,Nat.lt_trans hg.2 (Nat.lt_trans hm.2 ht.2)⟩
end BlockedSource
end DosenPetric.Reduced.Gentzen
