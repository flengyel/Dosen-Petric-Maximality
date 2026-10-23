module

public import DosenPetric.GentzenMixedInjections

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- The source branching left-thinning calculation, before context-fold comparisons. -/
theorem branchL_core (X Y A B : NormalForm P) (f : Hom X Y) :
    comp (tensor .conj (id (.disj A B)) (diag X))
      (comp (swap .conj (.disj A B) (.conj X X))
        (comp (ofTerm (Rules.sourceConj X X A B))
          (comp (tensor .disj (fst X A) (fst X B))
            (comp (tensor .disj f f) (codiag Y))))) =
      comp (snd (.disj A B) X) f := by
  rw [← Laws.assoc (ofTerm (Rules.sourceConj X X A B)), sourceConj_fst]
  simp only [← Laws.assoc]
  rw [← Laws.swap_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (diag X) (id (.disj A B))), ← Laws.fst_nat]
  simp only [← Laws.assoc]
  rw [← Laws.snd_swap]
  simp only [Laws.assoc]
  have hff : comp (diag X) (comp (mix X X) (comp (tensor .disj f f) (codiag Y))) = f :=
    (union_source f f).symm.trans (union_idem f)
  exact congrArg (fun k => comp (snd (.disj A B) X) k) hff

/-- The exact dual calculation for the mixedDisj used by conjunction-right. -/
theorem branchR_core (X Y A B : NormalForm P) (f : Hom X Y) :
    comp (diag X)
      (comp (tensor .conj (comp f (inr A Y)) (comp f (inr B Y)))
        (comp (ofTerm (Term.mixedDisj A Y B Y)) (tensor .disj (id (.conj A B)) (codiag Y)))) =
      comp f (inr (.conj A B) Y) := by
  rw [← Laws.tensor_comp]
  simp only [Laws.assoc]
  rw [← Laws.assoc (diag X), Laws.diag_nat]
  rw [← Laws.assoc (tensor .conj (inr A Y) (inr B Y)), mixedDisj_inr]
  simp only [Laws.assoc]
  rw [Laws.inr_nat]
  have h := congrArg (fun k => comp f (comp k (inr (.conj A B) Y)))
    (Laws.diag_mix_codiag Y)
  simpa only [Laws.assoc, Laws.id_comp] using h

end DosenPetric.Reduced.Gentzen
