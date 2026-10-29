module

public import DosenPetric.GentzenConjFirstSelected

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

/-- A selected output cut commutes with right distribution past a fixed factor. -/
theorem splice_distRight {X Y C R E T Z : NormalForm P}
    (f : Hom X (.disj C R)) (g : Hom Y E) (h : Hom (.conj C T) Z) :
    splice (comp (tensor .conj f g) (distRight C R E)) h =
      comp (assocR .conj T X Y)
        (comp (tensor .conj (splice f h) g) (distRight Z R E)) := by
  symm
  unfold splice
  have ht : tensor .conj
      (comp (tensor .conj (id T) f)
        (comp (dist T C R) (tensor .disj (comp (swap .conj T C) h) (id R)))) g =
      comp (tensor .conj (tensor .conj (id T) f) g)
        (comp (tensor .conj (dist T C R) (id E))
          (tensor .conj (tensor .disj (comp (swap .conj T C) h) (id R)) (id E))) := by
    simp only [Laws.tensor_comp,Laws.comp_id]
  rw [ht]
  simp only [Laws.assoc]
  have hn := Laws.distRight_nat (comp (swap .conj T C) h) (id R) (id E)
  rw [Laws.tensor_id] at hn
  rw [← hn]
  rw [← Laws.assoc (tensor .conj (dist T C R) (id E)),Laws.dist_b_conj]
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocR .conj T X Y),Laws.assocR_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocR .conj T (.disj C R) E),Laws.assocR_L,Laws.id_comp]
  rw [← Laws.assoc (tensor .conj (id T) (tensor .conj f g)),Laws.tensor_comp,Laws.id_comp]

end BinaryLogical
end DosenPetric.Reduced.Gentzen
