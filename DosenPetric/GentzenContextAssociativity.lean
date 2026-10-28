module

public import DosenPetric.GentzenPrincipalConjunction
public import DosenPetric.GentzenContextNormalizationLaws

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ExchangeScript

def appendAssoc (Γ Δ Θ : List (NormalForm P)) :
    ExchangeScript P (Γ ++ (Δ ++ Θ)) ((Γ ++ Δ) ++ Θ) :=
  (ExchangeScript.identity ((Γ ++ Δ) ++ Θ)).reindex (List.append_assoc Γ Δ Θ) rfl

theorem appendAssoc_first {Γ : List (NormalForm P)} (Δ Θ : List (NormalForm P))
    {A : NormalForm P} (a : At Γ A) :
    (appendAssoc Γ Δ Θ).get ((a.before Δ).before Θ) = a.before (Δ ++ Θ) := by
  apply At.index_injective
  simp only [appendAssoc, get, rewire, Rewire.get, At.index_cast, At.index_before]

theorem appendAssoc_second (Γ : List (NormalForm P)) {Δ : List (NormalForm P)}
    (Θ : List (NormalForm P)) {A : NormalForm P} (a : At Δ A) :
    (appendAssoc Γ Δ Θ).get ((At.shift Γ a).before Θ) = At.shift Γ (a.before Θ) := by
  apply At.index_injective
  simp only [appendAssoc, get, rewire, Rewire.get, At.index_cast, At.index_before, At.index_shift]

theorem appendAssoc_third (Γ Δ : List (NormalForm P)) {Θ : List (NormalForm P)}
    {A : NormalForm P} (a : At Θ A) :
    (appendAssoc Γ Δ Θ).get (At.shift (Γ ++ Δ) a) = At.shift Γ (At.shift Δ a) := by
  apply At.index_injective
  simp only [appendAssoc, get, rewire, Rewire.get, At.index_cast, At.index_shift,
    List.length_append, Nat.add_assoc]

end ExchangeScript

/-- Associativity of the actual fold comparisons, including all unit contexts. -/
theorem join_assoc (o : Op) (Γ Δ Θ : List (NormalForm P)) :
    (side P o).comp ((sideM P o).tensor (join o Γ Δ) ((side P o).id (fold o Θ)))
        (join o (Γ ++ Δ) Θ) =
      (side P o).comp ((sideM P o).assocL (fold o Γ) (fold o Δ) (fold o Θ))
        ((side P o).comp ((sideM P o).tensor ((side P o).id (fold o Γ)) (join o Δ Θ))
          ((side P o).comp (join o Γ (Δ ++ Θ)) ((ExchangeScript.appendAssoc Γ Δ Θ).arrow o))) := by
  let C := side P o
  let D := sideD P o
  apply side_ext o
  intro A a
  cases At.cases_append (Γ ++ Δ) Θ a with
  | inr h =>
    obtain ⟨a,rfl⟩ := h
    rw [C.assoc, join_shift, ← C.assoc, ← D.snd_nat, C.comp_id]
    rw [C.assoc, C.assoc, C.assoc, ExchangeScript.component, ExchangeScript.appendAssoc_third,
      join_shift, ← C.assoc ((sideM P o).tensor _ _), ← D.snd_nat,
      C.assoc, join_shift]
    have hh := congrArg (fun k => C.comp k (component o a))
      (logical_head_tail o (fold o Γ) (fold o Δ) (fold o Θ))
    cases o <;> dsimp only [C, side, category, opposite] at hh ⊢
    all_goals simpa only [Laws.assoc] using hh.symm
  | inl h =>
    obtain ⟨a,rfl⟩ := h
    cases At.cases_append Γ Δ a with
    | inl h =>
      obtain ⟨a,rfl⟩ := h
      rw [C.assoc, join_before, ← C.assoc, ← D.fst_nat, C.assoc, join_before]
      rw [C.assoc, C.assoc, C.assoc, ExchangeScript.component, ExchangeScript.appendAssoc_first,
        join_before, ← C.assoc ((sideM P o).tensor _ _), ← D.fst_nat, C.comp_id]
      have hh := congrArg (fun k => C.comp k (component o a))
        (logical_head_first o (fold o Γ) (fold o Δ) (fold o Θ))
      cases o <;> dsimp only [C, side, category, opposite] at hh ⊢
      all_goals simpa only [Laws.assoc] using hh.symm
    | inr h =>
      obtain ⟨a,rfl⟩ := h
      rw [C.assoc, join_before, ← C.assoc, ← D.fst_nat, C.assoc, join_shift]
      rw [C.assoc, C.assoc, C.assoc, ExchangeScript.component, ExchangeScript.appendAssoc_second,
        join_shift, ← C.assoc ((sideM P o).tensor _ _), ← D.snd_nat, C.assoc, join_before]
      have hh := congrArg (fun k => C.comp k (component o a))
        (logical_head_second o (fold o Γ) (fold o Δ) (fold o Θ))
      cases o <;> dsimp only [C, side, category, opposite] at hh ⊢
      all_goals simpa only [Laws.assoc] using hh.symm

end DosenPetric.Reduced.Gentzen
