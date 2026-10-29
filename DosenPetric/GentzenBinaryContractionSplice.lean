module

public import DosenPetric.GentzenSpliceSelectedNaturality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.ContractionSplice
universe u
variable {P : Type u}

/-- A two-copy contraction expands to two splices with the same original
    premise; its fixed input and residual output are contracted explicitly. -/
theorem binary {C X Y R Z : NormalForm P} (h : Hom X (.disj C R))
    (g : Hom (.conj C (.conj C Y)) Z) :
    splice h (comp (tensor .conj (diag C) (id Y))
      (comp (assocL .conj C C Y) g)) =
      comp (tensor .conj (id Y) (diag X))
        (comp (assocR .conj Y X X)
          (comp (splice h (comp (assocR .conj C Y X) (splice h g)))
            (comp (assocL .disj Z R R) (tensor .disj (id Z) (codiag R))))) := by
  rw [Splice.selected,← duplicate_output h]
  rw [← Laws.assoc (pair h h),Splice.residual]
  rw [pair,Laws.assoc,Splice.input,PrincipalConjunction.equation]
  simp only [Laws.assoc]

end DosenPetric.Reduced.Gentzen.ContractionSplice
