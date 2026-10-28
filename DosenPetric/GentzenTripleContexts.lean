module

public import DosenPetric.GentzenContextAssociativity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

def tripleIso (o : Op) (Γ Δ Θ : List (NormalForm P)) :
    Iso (o.formula (o.formula (fold o Γ) (fold o Δ)) (fold o Θ)) (fold o (Γ ++ (Δ ++ Θ))) :=
  (Iso.assoc o (fold o Γ) (fold o Δ) (fold o Θ)).trans
    ((Iso.tensor o (Iso.refl (fold o Γ)) (append o Δ Θ)).trans (append o Γ (Δ ++ Θ)))

def joinThree (o : Op) (Γ Δ Θ : List (NormalForm P)) :
    (side P o).Hom ((sideM P o).obj ((sideM P o).obj (fold o Γ) (fold o Δ)) (fold o Θ))
      (fold o (Γ ++ (Δ ++ Θ))) :=
  match o with
  | .conj => ofTerm (tripleIso .conj Γ Δ Θ).toTerm
  | .disj => ofTerm (tripleIso .disj Γ Δ Θ).invTerm

def splitThree (o : Op) (Γ Δ Θ : List (NormalForm P)) :
    (side P o).Hom (fold o (Γ ++ (Δ ++ Θ)))
      ((sideM P o).obj ((sideM P o).obj (fold o Γ) (fold o Δ)) (fold o Θ)) :=
  match o with
  | .conj => ofTerm (tripleIso .conj Γ Δ Θ).invTerm
  | .disj => ofTerm (tripleIso .disj Γ Δ Θ).toTerm

theorem joinThree_eq (o : Op) (Γ Δ Θ : List (NormalForm P)) :
    joinThree o Γ Δ Θ =
      (side P o).comp ((sideM P o).assocL (fold o Γ) (fold o Δ) (fold o Θ))
        ((side P o).comp ((sideM P o).tensor ((side P o).id (fold o Γ)) (join o Δ Θ))
          (join o Γ (Δ ++ Θ))) := by
  cases o <;> simp only [joinThree, tripleIso, Iso.trans, Iso.assoc,
    Iso.tensor, Iso.refl, ofTerm_comp, ofTerm_tensor, ofTerm_id] <;> rfl

theorem splitThree_eq (o : Op) (Γ Δ Θ : List (NormalForm P)) :
    splitThree o Γ Δ Θ =
      (side P o).comp (split o Γ (Δ ++ Θ))
        ((side P o).comp ((sideM P o).tensor ((side P o).id (fold o Γ)) (split o Δ Θ))
          ((sideM P o).assocR (fold o Γ) (fold o Δ) (fold o Θ))) := by
  cases o <;> dsimp only [splitThree, tripleIso, Iso.trans, Iso.assoc, Iso.tensor,
    Iso.refl, side, sideM, conjMonoidal, disjMonoidal, category, opposite, split]
  all_goals simp only [ofTerm_comp, ofTerm_tensor, ofTerm_id, Laws.assoc]
  all_goals rfl

theorem joinThree_splitThree (o : Op) (Γ Δ Θ : List (NormalForm P)) :
    (side P o).comp (joinThree o Γ Δ Θ) (splitThree o Γ Δ Θ) = (side P o).id _ := by
  cases o with
  | conj => exact (tripleIso .conj Γ Δ Θ).to_inv
  | disj => exact (tripleIso .disj Γ Δ Θ).to_inv

theorem splitThree_joinThree (o : Op) (Γ Δ Θ : List (NormalForm P)) :
    (side P o).comp (splitThree o Γ Δ Θ) (joinThree o Γ Δ Θ) = (side P o).id _ := by
  cases o with
  | conj => exact (tripleIso .conj Γ Δ Θ).inv_to
  | disj => exact (tripleIso .disj Γ Δ Θ).inv_to

theorem leftThree_join_split (o : Op) (Γ Δ Θ : List (NormalForm P)) :
    (side P o).comp
        ((side P o).comp ((sideM P o).tensor (join o Γ Δ) ((side P o).id (fold o Θ)))
          (join o (Γ ++ Δ) Θ))
        ((side P o).comp (split o (Γ ++ Δ) Θ)
          ((sideM P o).tensor (split o Γ Δ) ((side P o).id (fold o Θ)))) = (side P o).id _ := by
  let i := (Iso.tensor o (append o Γ Δ) (Iso.refl (fold o Θ))).trans (append o (Γ ++ Δ) Θ)
  cases o <;> dsimp only [side, sideM, conjMonoidal, disjMonoidal,
    category, opposite, join, split]
  all_goals simpa only [i, Iso.trans, Iso.tensor, Iso.refl,
    ofTerm_comp, ofTerm_tensor, ofTerm_id, Laws.assoc] using i.to_inv

/-- The input comparison for nested cuts; equality transport does not add an exchange. -/
theorem split_assoc (o : Op) (Γ Δ Θ : List (NormalForm P)) :
    (side P o).comp ((ExchangeScript.appendAssoc Γ Δ Θ).arrow o)
        ((side P o).comp (split o (Γ ++ Δ) Θ)
          ((sideM P o).tensor (split o Γ Δ) ((side P o).id (fold o Θ)))) =
      (side P o).comp (split o Γ (Δ ++ Θ))
        ((side P o).comp ((sideM P o).tensor ((side P o).id (fold o Γ)) (split o Δ Θ))
          ((sideM P o).assocR (fold o Γ) (fold o Δ) (fold o Θ))) := by
  let C := side P o
  rw [← splitThree_eq]
  apply DiagonalData.cancel_left (C := C) _ _ (joinThree o Γ Δ Θ) (splitThree o Γ Δ Θ)
    (splitThree_joinThree o Γ Δ Θ)
  have hj : C.comp (joinThree o Γ Δ Θ) ((ExchangeScript.appendAssoc Γ Δ Θ).arrow o) =
      C.comp ((sideM P o).tensor (join o Γ Δ) (C.id (fold o Θ))) (join o (Γ ++ Δ) Θ) := by
    rw [joinThree_eq]
    have he := (join_assoc o Γ Δ Θ).symm
    cases o <;> dsimp only [C, side, category, opposite] at he ⊢
    all_goals simpa only [Laws.assoc] using he
  rw [← C.assoc, hj, leftThree_join_split, joinThree_splitThree]

theorem split_cons (o : Op) (A : NormalForm P) (Γ Δ : List (NormalForm P)) :
    split o (A :: Γ) Δ =
      (side P o).comp ((sideM P o).tensor ((side P o).id A) (split o Γ Δ))
        ((sideM P o).assocR A (fold o Γ) (fold o Δ)) := by
  cases o <;> simp only [split, append, Iso.trans, Iso.assoc, Iso.tensor, Iso.refl,
    ofTerm_comp, ofTerm_tensor, ofTerm_id] <;> rfl

end DosenPetric.Reduced.Gentzen
