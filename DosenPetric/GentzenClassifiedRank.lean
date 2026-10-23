module

public import DosenPetric.GentzenRuleClassification
public import DosenPetric.GentzenClusterRank

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace G

/-- The source's lower contraction formula, selected by the rule indices. -/
inductive LowerContraction : {Γ Δ : List (NormalForm P)} → (g : G P Γ Δ) →
    (s : SequentSide) → {C : NormalForm P} → Place s Γ Δ C → Prop where
  | left (C gs Θ Δ hn) (f : G P (repeated C gs ++ Θ) Δ) :
      LowerContraction (contractL C gs Θ Δ hn f) .left (At.shift (gaps gs) (.here C Θ))
  | right (Γ C gs Λ hn) (f : G P Γ (repeated C gs ++ Λ)) :
      LowerContraction (contractR Γ C gs Λ hn f) .right (At.shift (gaps gs) (.here C Λ))

theorem lowerContractionL_of_index (A : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Δ : List (NormalForm P)) (hn : 2 ≤ gs.length) (f : G P (repeated A gs ++ Θ) Δ)
    {C : NormalForm P} (x : At (gaps gs ++ A :: Θ) C) (hi : x.index = (gaps gs).length) :
    LowerContraction (contractL A gs Θ Δ hn f) .left x := by
  cases h : At.compare x (At.shift (gaps gs) (.here A Θ)) with
  | same => exact .left A gs Θ Δ hn f
  | apart hh =>
    apply False.elim
    apply hh
    simpa only [At.index_shift,At.index,Nat.add_zero] using hi

theorem lowerContractionR_of_index (Γ : List (NormalForm P)) (A : NormalForm P)
    (gs : List (List (NormalForm P))) (Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (f : G P Γ (repeated A gs ++ Λ)) {C : NormalForm P}
    (x : At (gaps gs ++ A :: Λ) C) (hi : x.index = (gaps gs).length) :
    LowerContraction (contractR Γ A gs Λ hn f) .right x := by
  cases h : At.compare x (At.shift (gaps gs) (.here A Λ)) with
  | same => exact .right Γ A gs Λ hn f
  | apart hh =>
    apply False.elim
    apply hh
    simpa only [At.index_shift,At.index,Nat.add_zero] using hi

theorem lowerContraction_iff_arity {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : LowerContraction g s x ↔ 2 ≤ g.sourceArity s x := by
  constructor
  · intro h
    cases h with
    | left C gs Θ Δ hn f =>
      change 2 ≤ if (At.shift (gaps gs) (.here C Θ)).index = (gaps gs).length then gs.length else 1
      have hi : (At.shift (gaps gs) (.here C Θ)).index = (gaps gs).length := by simp [At.index_shift,At.index]
      rw [ite_eq_left hi]
      exact hn
    | right Γ C gs Λ hn f =>
      change 2 ≤ if (At.shift (gaps gs) (.here C Λ)).index = (gaps gs).length then gs.length else 1
      have hi : (At.shift (gaps gs) (.here C Λ)).index = (gaps gs).length := by simp [At.index_shift,At.index]
      rw [ite_eq_left hi]
      exact hn
  · intro h
    cases g <;> cases s <;> simp only [sourceArity] at h
    all_goals try omega
    all_goals split at h
    all_goals try omega
    all_goals first
      | apply lowerContractionL_of_index; assumption
      | apply lowerContractionR_of_index; assumption

/-- Exhaustive source classification, with exact computed branch counts. -/
theorem position_classification {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : g.Leaf s x ∨ g.Parametric s x ∨ LowerContraction g s x := by
  by_cases h₀ : g.sourceArity s x = 0
  · exact .inl h₀
  · by_cases h₁ : g.sourceArity s x = 1
    · exact .inr (.inl h₁)
    · exact .inr (.inr ((g.lowerContraction_iff_arity s x).mpr (by omega)))

theorem position_classes_disjoint {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) :
    ¬ (g.Leaf s x ∧ g.Parametric s x) ∧
    ¬ (g.Leaf s x ∧ LowerContraction g s x) ∧
    ¬ (g.Parametric s x ∧ LowerContraction g s x) := by
  rw [lowerContraction_iff_arity]
  unfold Leaf Parametric
  omega

theorem rho_one_iff_leaf {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : g.rho s x = 1 ↔ g.Leaf s x :=
  (g.rho_one_iff s x).trans (g.leaf_iff_no_predecessor s x).symm

theorem rho_leaf {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) (h : g.Leaf s x) : g.rho s x = 1 :=
  (g.rho_one_iff_leaf s x).mpr h

theorem rho_parametric {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) (h : g.Parametric s x) :
    ∃ a : Upper g s C, g.predecessors s x = [a] ∧
      g.rho s x = 1 + a.branch.proof.rho s a.position := by
  obtain ⟨a,ha,_⟩ := g.parametric_unique s x h
  refine ⟨a,ha,?_⟩
  rw [rho_eq,ha]
  rfl

theorem contraction_predecessorsL (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Δ : List (NormalForm P)) (hn : 2 ≤ gs.length) (f : G P (repeated C gs ++ Θ) Δ) :
    (contractL C gs Θ Δ hn f).predecessors .left (At.shift (gaps gs) (.here C Θ)) =
      (selectedCopies C gs Θ).map (fun (y : At (repeated C gs ++ Θ) C) =>
        (⟨⟨_,_,f,Premise.contractL C gs Θ Δ hn f⟩,y⟩ : Upper (contractL C gs Θ Δ hn f) .left C)) := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change ((TraceRoute.full (copies C gs Θ)).fiber (At.shift (gaps gs) (.here C Θ))).map _ = _
  rw [fiber_copies_selected]
  rfl

theorem contraction_predecessorsR (Γ : List (NormalForm P)) (C : NormalForm P)
    (gs : List (List (NormalForm P))) (Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (f : G P Γ (repeated C gs ++ Λ)) :
    (contractR Γ C gs Λ hn f).predecessors .right (At.shift (gaps gs) (.here C Λ)) =
      (selectedCopies C gs Λ).map (fun (y : At (repeated C gs ++ Λ) C) =>
        (⟨⟨_,_,f,Premise.contractR Γ C gs Λ hn f⟩,y⟩ : Upper (contractR Γ C gs Λ hn f) .right C)) := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change ((TraceRoute.full (copies C gs Λ)).fiber (At.shift (gaps gs) (.here C Λ))).map _ = _
  rw [fiber_copies_selected]
  rfl

theorem contractionRankL_eq (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Δ : List (NormalForm P)) (hn : 2 ≤ gs.length) (f : G P (repeated C gs ++ Θ) Δ) :
    contractionRankL C gs Θ Δ hn f = 1 + ((selectedCopies C gs Θ).map
      (fun (x : At (repeated C gs ++ Θ) C) => f.rho .left x)).sum := by
  have hs := congrArg (fun us : List (Upper (contractL C gs Θ Δ hn f) .left C) =>
    1 + (us.map (fun a => a.branch.proof.rho .left a.position)).sum)
    (contraction_predecessorsL C gs Θ Δ hn f)
  exact ((contractL C gs Θ Δ hn f).rho_eq .left (At.shift (gaps gs) (.here C Θ))).trans
    (by simpa only [List.map_map,Function.comp_def] using hs)

theorem contractionRankR_eq (Γ : List (NormalForm P)) (C : NormalForm P)
    (gs : List (List (NormalForm P))) (Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (f : G P Γ (repeated C gs ++ Λ)) :
    contractionRankR Γ C gs Λ hn f = 1 + ((selectedCopies C gs Λ).map
      (fun (x : At (repeated C gs ++ Λ) C) => f.rho .right x)).sum := by
  have hs := congrArg (fun us : List (Upper (contractR Γ C gs Λ hn f) .right C) =>
    1 + (us.map (fun a => a.branch.proof.rho .right a.position)).sum)
    (contraction_predecessorsR Γ C gs Λ hn f)
  exact ((contractR Γ C gs Λ hn f).rho_eq .right (At.shift (gaps gs) (.here C Λ))).trans
    (by simpa only [List.map_map,Function.comp_def] using hs)

theorem cutRank_two_iff_leaves {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) :
    cutRank f g = 2 ↔ f.Leaf .right (.here C Δ) ∧ g.Leaf .left (.here C Θ) := by
  rw [cutRank_eq_two]
  exact and_congr (f.rho_one_iff_leaf .right (.here C Δ)) (g.rho_one_iff_leaf .left (.here C Θ))

end G
end DosenPetric.Reduced.Gentzen
