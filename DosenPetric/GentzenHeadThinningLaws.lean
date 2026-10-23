module

public import DosenPetric.GentzenBlockComparisons
public import DosenPetric.GentzenThinningCore

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem thin_head (o : Op) (A : NormalForm P) (Γ : List (NormalForm P)) :
    (Route.thin [] Γ A).sideArrow o = (sideD P o).snd A (fold o Γ) := by
  apply side_ext o
  intro B a
  rw [Route.sideArrow_get]
  simp only [Route.thin, Route.get_map, Route.get_identity, component_there]

theorem conjLeft_head (Γ : List (NormalForm P)) (A B : NormalForm P) :
    ofTerm (Rules.conjLeft [] Γ A B).toTerm = assocL .conj A B (ante Γ) := by
  have hi : Rules.conjLeft [] Γ A B = Iso.assoc .conj A B (ante Γ) := by
    unfold Rules.conjLeft
    apply eq_of_heq
    change (cast _ (cast _ (Iso.assoc .conj A B (ante Γ)))) ≍ _
    exact (cast_heq _ _).trans (cast_heq _ _)
  rw [hi]
  rfl

theorem disjRight_head (Δ : List (NormalForm P)) (A B : NormalForm P) :
    ofTerm (Rules.disjRight [] Δ A B).toTerm = assocR .disj A B (succ Δ) := by
  have hi : Rules.disjRight [] Δ A B = (Iso.assoc .disj A B (succ Δ)).symm := by
    unfold Rules.disjRight
    apply eq_of_heq
    change (cast _ (cast _ (Iso.assoc .disj A B (succ Δ)).symm)) ≍ _
    exact (cast_heq _ _).trans (cast_heq _ _)
  rw [hi]
  rfl

theorem conj_thin_head (A B X : NormalForm P) :
    comp (assocL .conj A B X) (comp (snd A (.conj B X)) (snd B X)) = snd (.conj A B) X := by
  have h : comp (assocR .conj A B X) (snd (.conj A B) X) =
      comp (snd A (.conj B X)) (snd B X) := (conjDiagonal P).assocR_snd A B X
  have hh := congrArg (fun k => comp (assocL .conj A B X) k) h
  rw [← Laws.assoc, Laws.assocL_R, Laws.id_comp] at hh
  exact hh.symm

theorem disj_thin_head (A B Y : NormalForm P) :
    comp (inr B Y) (comp (inr A (.disj B Y)) (assocR .disj A B Y)) = inr (.disj A B) Y := by
  have h : comp (inr (.disj A B) Y) (assocL .disj A B Y) =
      comp (inr B Y) (inr A (.disj B Y)) := (disjDiagonal P).assocR_snd A B Y
  have hh := congrArg (fun k => comp k (assocR .disj A B Y)) h
  rw [Laws.assoc, Laws.assocL_R, Laws.comp_id] at hh
  exact (Laws.assoc ..).symm.trans hh.symm

/-- Both duplicated antecedent and succedent blocks are contracted. -/
theorem branchL_denote (Γ Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : Term P (ante Γ) (succ Δ)) :
    comp ((Rewire.dupTail (.disj A B) Γ).arrow .conj)
      (comp (ofTerm (Rules.disjLeft (.comp (.snd A (ante Γ)) f) (.comp (.snd B (ante Γ)) f)))
        ((Rewire.dupContext Δ).arrow .disj)) =
      comp (snd (.disj A B) (ante Γ)) (ofTerm f) := by
  rw [Rewire.dupTail_arrow, Rewire.dupContext_arrow]
  change comp (tensor .conj (id (.disj A B)) (comp (diag (ante Γ)) (ofTerm (append .conj Γ Γ).toTerm)))
    (comp (ofTerm (Rules.disjLeft (.comp (.snd A (ante Γ)) f) (.comp (.snd B (ante Γ)) f)))
      (comp (ofTerm (append .disj Δ Δ).invTerm) (codiag (succ Δ)))) = _
  simp only [Rules.disjLeft, ofTerm_comp, ofTerm_tensor, ofTerm_id, term_swap, Laws.assoc]
  rw [← Laws.assoc (ofTerm (append .disj Δ Δ).toTerm), (append .disj Δ Δ).to_inv, Laws.id_comp]
  rw [← Laws.assoc (tensor .conj (id (.disj A B))
      (comp (diag (ante Γ)) (ofTerm (append .conj Γ Γ).toTerm))), Laws.tensor_comp,
    Laws.id_comp, Laws.assoc, (append .conj Γ Γ).to_inv, Laws.comp_id]
  rw [← Laws.assoc (tensor .disj (swap .conj (ante Γ) A) (swap .conj (ante Γ) B)), Laws.tensor_comp]
  have ha : comp (swap .conj (ante Γ) A) (ofTerm (.comp (.snd A (ante Γ)) f)) =
      comp (fst (ante Γ) A) (ofTerm f) := by
    change comp (swap .conj (ante Γ) A) (comp (snd A (ante Γ)) (ofTerm f)) = _
    rw [← Laws.assoc, swap_snd]
  have hb : comp (swap .conj (ante Γ) B) (ofTerm (.comp (.snd B (ante Γ)) f)) =
      comp (fst (ante Γ) B) (ofTerm f) := by
    change comp (swap .conj (ante Γ) B) (comp (snd B (ante Γ)) (ofTerm f)) = _
    rw [← Laws.assoc, swap_snd]
  simp only [ofTerm_comp] at ha hb
  rw [ha, hb, ← Laws.tensor_comp]
  simpa only [Laws.assoc] using branchL_core (ante Γ) (succ Δ) A B (ofTerm f)

theorem branchR_denote (Γ Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : Term P (ante Γ) (succ Δ)) :
    comp ((Rewire.dupContext Γ).arrow .conj)
      (comp (ofTerm (Rules.conjRight (.comp f (.inr A (succ Δ))) (.comp f (.inr B (succ Δ)))))
        ((Rewire.dupTail (.conj A B) Δ).arrow .disj)) =
      comp (ofTerm f) (inr (.conj A B) (succ Δ)) := by
  rw [Rewire.dupContext_arrow, Rewire.dupTail_arrow]
  change comp (comp (diag (ante Γ)) (ofTerm (append .conj Γ Γ).toTerm))
    (comp (ofTerm (Rules.conjRight (.comp f (.inr A (succ Δ))) (.comp f (.inr B (succ Δ)))))
      (tensor .disj (id (.conj A B)) (comp (ofTerm (append .disj Δ Δ).invTerm) (codiag (succ Δ))))) = _
  simp only [Rules.conjRight, ofTerm_comp, ofTerm_tensor, ofTerm_id, Laws.assoc]
  rw [← Laws.assoc (ofTerm (append .conj Γ Γ).toTerm), (append .conj Γ Γ).to_inv, Laws.id_comp]
  rw [Laws.tensor_comp, Laws.id_comp, ← Laws.assoc (ofTerm (append .disj Δ Δ).toTerm),
    (append .disj Δ Δ).to_inv, Laws.id_comp]
  exact branchR_core (ante Γ) (succ Δ) A B (ofTerm f)

end DosenPetric.Reduced.Gentzen
