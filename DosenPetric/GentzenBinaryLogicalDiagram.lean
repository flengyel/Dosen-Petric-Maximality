module

public import DosenPetric.GentzenBinaryLogicalAssociativity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

/-- Cut through the second factor of a native product before its logical comparison. -/
theorem product_right_splice {T C D E X Y Z : NormalForm P}
    (f : Hom X (.disj C D)) (g : Hom Y E) (h : Hom (.conj C T) Z) :
    splice f (comp ((sideM P .conj).cross C Y T) (tensor .conj g h)) =
      comp (assocL .conj Y T X)
        (comp (tensor .conj g (splice f h)) (dist E Z D)) := by
  symm
  unfold splice
  have ht : tensor .conj g
      (comp (tensor .conj (id T) f)
        (comp (dist T C D) (tensor .disj (comp (swap .conj T C) h) (id D)))) =
      comp (tensor .conj (id Y) (tensor .conj (id T) f))
        (comp (tensor .conj (id Y) (dist T C D))
          (tensor .conj g (tensor .disj (comp (swap .conj T C) h) (id D)))) := by
    simp only [Laws.tensor_comp,Laws.id_comp]
  rw [ht]
  simp only [Laws.assoc]
  rw [← Laws.dist_nat g (comp (swap .conj T C) h) (id D)]
  rw [← Laws.assoc (tensor .conj (id Y) (dist T C D)),CutDistribution.conjunction]
  simp only [Laws.assoc]
  have hn : comp (tensor .conj (id Y) (tensor .conj (id T) f))
      (assocR .conj Y T (.disj C D)) =
      comp (assocR .conj Y T X) (tensor .conj (id (.conj Y T)) f) := by
    simpa only [Laws.tensor_id] using (Laws.assocR_nat .conj (id Y) (id T) f).symm
  rw [← Laws.assoc (tensor .conj (id Y) (tensor .conj (id T) f)),hn]
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocL .conj Y T X),Laws.assocL_R,Laws.id_comp]
  have hh : tensor .conj g (comp (swap .conj T C) h) =
      comp (tensor .conj (id Y) (swap .conj T C)) (tensor .conj g h) := by
    rw [Laws.tensor_comp,Laws.id_comp]
  have hr : comp (assocL .conj Y T C) (tensor .conj g (comp (swap .conj T C) h)) =
      comp (swap .conj (.conj Y T) C)
        (comp ((sideM P .conj).cross C Y T) (tensor .conj g h)) := by
    rw [hh]
    have he := congrArg (fun k => comp (swap .conj (.conj Y T) C) (comp k (tensor .conj g h)))
      ((conjDiagonal P).dual_outer_route (rightOut_assocR .conj) (side_swap_snd .conj) Y C T)
    dsimp only [sideM,conjMonoidal,category] at he ⊢
    simpa only [Laws.assoc,BinaryMix.swap_twice] using he
  erw [Laws.tensor_comp,Laws.id_comp,hr]

/-- The residual output association in the actual conjunction-right comparison. -/
theorem mixed_residual (A D B E Z : NormalForm P) :
    comp (dist (.disj A D) (.disj B E) Z)
      (comp (tensor .disj (ofTerm (Term.mixedDisj A D B E)) (id Z))
        (comp (assocL .disj (.conj A B) (.disj D E) Z)
          (tensor .disj (id (.conj A B)) (assocL .disj D E Z)))) =
      comp (tensor .conj (id (.disj A D)) (assocL .disj B E Z))
        (ofTerm (Term.mixedDisj A D B (.disj E Z))) := by
  symm
  rw [mixedDisj_eq,mixedDisj_eq]
  rw [← Laws.assoc (tensor .conj (id (.disj A D)) (assocL .disj B E Z)),
    CutDistribution.disjunction]
  simp only [Laws.assoc]
  have hn : comp (assocL .disj (.conj (.disj A D) B) E Z)
      (tensor .disj (innerDisj A D B) (id (.disj E Z))) =
      comp (tensor .disj (tensor .disj (innerDisj A D B) (id E)) (id Z))
        (assocL .disj (.disj (.conj A B) D) E Z) := by
    simpa only [Laws.tensor_id] using Laws.assocL_nat .disj (innerDisj A D B) (id E) (id Z)
  rw [← Laws.assoc (assocL .disj (.conj (.disj A D) B) E Z),hn]
  simp only [Laws.assoc]
  rw [← disj_assocL_pentagon]
  rw [← Laws.assoc (tensor .disj (tensor .disj (innerDisj A D B) (id E)) (id Z)),
    Laws.tensor_comp,Laws.id_comp]
  rw [← Laws.assoc (tensor .disj (dist (.disj A D) B E) (id Z)),
    Laws.tensor_comp,Laws.id_comp]

end BinaryLogical
end DosenPetric.Reduced.Gentzen
