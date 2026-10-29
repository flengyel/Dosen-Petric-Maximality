module

public import DosenPetric.GentzenBlockedRightMixSource
public import DosenPetric.GentzenThinningCore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedConj
universe u
variable {P : Type u}

def lift {S A D : NormalForm P} (f : Hom S (.disj A D)) (R : NormalForm P) :
    Hom (.disj S R) (.disj A (.disj D R)) :=
  comp (tensor .disj f (id R)) (assocL .disj A D R)

theorem assocL_inl (A D R : NormalForm P) :
    comp (inl (.disj A D) R) (assocL .disj A D R) = tensor .disj (id A) (inl D R) :=
  (disjDiagonal P).assocR_fst (rightIn_assocL .disj) A D R

theorem assocL_inr (A D R : NormalForm P) :
    comp (inr (.disj A D) R) (assocL .disj A D R) =
      comp (inr D R) (inr A (.disj D R)) :=
  (disjDiagonal P).assocR_snd A D R

theorem lift_inl {S A D : NormalForm P} (f : Hom S (.disj A D)) (R : NormalForm P) :
    comp (inl S R) (lift f R) = comp f (tensor .disj (id A) (inl D R)) := by
  rw [lift,← Laws.assoc,Laws.inl_nat,Laws.assoc,assocL_inl]

theorem lift_inr {S A D : NormalForm P} (f : Hom S (.disj A D)) (R : NormalForm P) :
    comp (inr S R) (lift f R) = comp (inr D R) (inr A (.disj D R)) := by
  rw [lift,← Laws.assoc,Laws.inr_nat,Laws.id_comp,assocL_inr]

theorem merge_left (D E R : NormalForm P) :
    comp (tensor .disj (inl D R) (inl E R)) (BlockedMix.sharedOutput D E R) =
      inl (.disj D E) R := by
  unfold BlockedMix.sharedOutput
  rw [BlockedMix.tensor_copair]
  rw [Laws.inl_nat,Laws.inl_nat]
  have he := (disjDiagonal P).pair_eta (inl (.disj D E) R)
  change copair (comp (inl D E) (inl (.disj D E) R))
    (comp (inr D E) (inl (.disj D E) R)) = _ at he
  exact he

theorem merge_right (D E R : NormalForm P) :
    comp (tensor .disj (inr D R) (inr E R)) (BlockedMix.sharedOutput D E R) =
      comp (codiag R) (inr (.disj D E) R) := by
  unfold BlockedMix.sharedOutput
  rw [BlockedMix.tensor_copair,Laws.inr_nat,Laws.inr_nat,Laws.id_comp]
  have he : copair (id R) (id R) = codiag R := by
    simp only [copair,Laws.tensor_id,Laws.id_comp]
  rw [← he,BlockedMix.copair_post,Laws.id_comp]

/-- The two native branches share the same residual output; each old residual
    block retains all its own tags. -/
theorem lifted_pair {S A B D E R : NormalForm P}
    (f : Hom S (.disj A D)) (g : Hom S (.disj B E)) :
    comp (pair (lift f R) (lift g R))
      (comp (ofTerm (Term.mixedDisj A (.disj D R) B (.disj E R)))
        (tensor .disj (id (.conj A B)) (BlockedMix.sharedOutput D E R))) =
      lift (comp (pair f g) (ofTerm (Term.mixedDisj A D B E))) R := by
  apply Reduced.disj_ext
  · simp only [← Laws.assoc,ProductCalculation.pair_pre,lift_inl]
    rw [← BlockedMix.pair_tensor]
    have he := mixedDisj_nat (id A) (inl D R) (id B) (inl E R)
    rw [Laws.tensor_id] at he
    simp only [Laws.assoc]
    rw [← Laws.assoc (tensor .conj (tensor .disj (id A) (inl D R))
      (tensor .disj (id B) (inl E R))),← he]
    simp only [Laws.assoc]
    rw [Laws.tensor_comp,Laws.id_comp,merge_left]
  · simp only [← Laws.assoc,ProductCalculation.pair_pre,lift_inr]
    rw [← BlockedMix.pair_tensor]
    simp only [Laws.assoc]
    rw [← Laws.assoc (tensor .conj (inr A (.disj D R)) (inr B (.disj E R))),mixedDisj_inr]
    simp only [Laws.assoc]
    rw [Laws.inr_nat]
    unfold pair
    simp only [Laws.assoc]
    rw [← Laws.assoc (tensor .conj (inr D R) (inr E R)),← Laws.mix_nat]
    simp only [Laws.assoc]
    rw [← Laws.assoc (tensor .disj (inr D R) (inr E R)),merge_right]
    simp only [Laws.assoc]
    rw [← Laws.assoc (diag R),← Laws.assoc (comp (diag R) (mix R R)),
      Laws.assoc (diag R),Laws.diag_mix_codiag,Laws.id_comp]

end DosenPetric.Reduced.Gentzen.BlockedConj
