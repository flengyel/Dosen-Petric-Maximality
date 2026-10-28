module

public import DosenPetric.GentzenConjRightSecondSelected

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem innerDisj_distRight (A D B : NormalForm P) :
    innerDisj A D B =
      comp (tensor .conj (swap .disj A D) (id B))
        (comp (distRight D A B) (swap .disj D (.conj A B))) := by
  have hd : distRight D A B = comp (swap .conj (.disj D A) B)
      (comp (tensor .conj (id B) (swap .disj D A))
        (comp (dist B A D)
          (comp (tensor .disj (swap .conj B A) (id D)) (swap .disj (.conj A B) D)))) := rfl
  rw [innerDisj,hd]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (swap .disj A D) (id B)),← Laws.swap_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id B) (swap .disj A D)),Laws.tensor_comp,
    Laws.id_comp,Laws.swap_swap,Laws.tensor_id,Laws.id_comp]
  rw [Laws.swap_swap,Laws.comp_id]

theorem residual_cross (X Y Z : NormalForm P) :
    comp (swap .disj (.disj X Y) Z)
      (comp (assocR .disj Z X Y)
        (comp (tensor .disj (swap .disj Z X) (id Y)) (assocL .disj X Z Y))) =
      comp (assocL .disj X Y Z) (tensor .disj (id X) (swap .disj Y Z)) := by
  have he := congrArg (fun k => comp (swap .disj (.disj X Y) Z)
    (comp k (comp (assocL .disj X Y Z) (tensor .disj (id X) (swap .disj Y Z)))) )
      (Laws.hexagon .disj Z X Y)
  simp only [Laws.assoc] at he
  rw [← Laws.assoc (swap .disj (.disj X Y) Z),Laws.swap_swap,Laws.id_comp] at he
  rw [← Laws.assoc (assocR .disj X Y Z),Laws.assocR_L,Laws.id_comp] at he
  rw [Laws.tensor_comp,
    Laws.id_comp,Laws.swap_swap,Laws.tensor_id,Laws.comp_id] at he
  exact he.symm

theorem mixedDisj_swap (A D B E : NormalForm P) :
    ofTerm (Term.mixedDisj A D B E) =
      comp (swap .conj (.disj A D) (.disj B E))
        (comp (ofTerm (Term.mixedDisj B E A D))
          (tensor .disj (swap .conj B A) (swap .disj E D))) := by
  rw [mixedDisj_eq,mixedDisj_eq,innerDisj_distRight A D B]
  have ht : tensor .disj
      (comp (tensor .conj (swap .disj A D) (id B))
        (comp (distRight D A B) (swap .disj D (.conj A B)))) (id E) =
      comp (tensor .disj (tensor .conj (swap .disj A D) (id B)) (id E))
        (comp (tensor .disj (distRight D A B) (id E))
          (tensor .disj (swap .disj D (.conj A B)) (id E))) := by
    simp only [Laws.tensor_comp,Laws.id_comp]
  rw [ht]
  simp only [Laws.assoc]
  rw [← Laws.assoc (dist (.disj A D) B E),Laws.dist_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (dist (.disj D A) B E),Laws.dist_b_disj]
  simp only [Laws.assoc]
  have hd : distRight D A (.disj B E) = comp (swap .conj (.disj D A) (.disj B E))
      (comp (tensor .conj (id (.disj B E)) (swap .disj D A))
        (comp (dist (.disj B E) A D)
          (comp (tensor .disj (swap .conj (.disj B E) A) (id D))
            (swap .disj (.conj A (.disj B E)) D)))) := rfl
  rw [hd,Laws.tensor_id]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (swap .disj A D) (id (.disj B E))),← Laws.swap_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id (.disj B E)) (swap .disj A D)),Laws.tensor_comp,
    Laws.id_comp,Laws.swap_swap,Laws.tensor_id,Laws.id_comp]
  have hc := residual_cross (.conj A B) E D
  rw [← Laws.assoc (swap .disj (.conj A (.disj B E)) D),Laws.swap_nat]
  simp only [Laws.assoc]
  rw [hc]
  have hf : tensor .disj (swap .conj B A) (swap .disj E D) =
      comp (tensor .disj (swap .conj B A) (id (.disj E D)))
        (tensor .disj (id (.conj A B)) (swap .disj E D)) := by
    rw [Laws.tensor_comp,Laws.comp_id,Laws.id_comp]
  rw [hf]
  have hn := Laws.assocL_nat .disj (swap .conj B A) (id E) (id D)
  rw [Laws.tensor_id] at hn
  rw [← Laws.assoc (assocL .disj (.conj B A) E D),hn]
  simp only [Laws.assoc]
  have hi : comp (innerDisj B E A) (tensor .disj (swap .conj B A) (id E)) =
      comp (swap .conj (.disj B E) A) (dist A B E) := by
    simp only [innerDisj,Laws.assoc]
    rw [Laws.tensor_comp,Laws.swap_swap,Laws.id_comp,Laws.tensor_id,Laws.comp_id]
  rw [← Laws.assoc (tensor .disj (innerDisj B E A) (id D)),Laws.tensor_comp,
    hi,Laws.id_comp]
  rw [← Laws.assoc (tensor .disj (swap .conj (.disj B E) A) (id D)),Laws.tensor_comp,
    Laws.id_comp]

end BinaryLogical
end DosenPetric.Reduced.Gentzen
