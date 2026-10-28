module

public import DosenPetric.GentzenMixUnion
public import DosenPetric.GentzenCutDistribution
public import DosenPetric.GentzenProductCalculations

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryMix

/-- The product comparison in the strength/mix diagram. -/
theorem assocL_fst (A B C : NormalForm P) :
    comp (assocL .conj A B C) (tensor .conj (id A) (fst B C)) = fst (.conj A B) C := by
  simp only [ProductCalculation.assocL_pair,ProductCalculation.tensor_pair,
    ProductCalculation.pair_pre,ProductCalculation.pair_fst,
    ProductCalculation.pair_snd_comp,Laws.comp_id]
  exact (conjDiagonal P).pair_eta (fst (.conj A B) C)

/-- Mix and distribution commute with reassociation of their product context. -/
theorem mix_strength (A B E : NormalForm P) :
    comp (assocR .conj A B E) (mix (.conj A B) E) =
      comp (tensor .conj (id A) (mix B E)) (dist A B E) := by
  rw [Laws.dist_mix (.conj A B) .top E,Laws.dist_mix B .top E]
  have hp := assocL_fst A B (.top : NormalForm P)
  rw [← hp]
  rw [tensor_factor .conj (id A) (tensor .conj (id B) (inr .top E)),
    tensor_factor .conj (id A) (dist B .top E)]
  have hn : comp (assocR .conj A B E) (tensor .conj (id (.conj A B)) (inr .top E)) =
      comp (tensor .conj (id A) (tensor .conj (id B) (inr .top E)))
        (assocR .conj A B (.disj .top E)) := by
    simpa only [Laws.tensor_id] using Laws.assocR_nat .conj (id A) (id B) (inr .top E)
  have ht : tensor .disj (comp (assocL .conj A B .top) (tensor .conj (id A) (fst B .top))) (id E) =
      comp (tensor .disj (assocL .conj A B .top) (id E))
        (tensor .disj (tensor .conj (id A) (fst B .top)) (id E)) := by
    rw [Laws.tensor_comp,Laws.id_comp]
  rw [ht]
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocR .conj A B E),hn]
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocR .conj A B (.disj .top E)),
    ← Laws.assoc (comp (assocR .conj A B (.disj .top E)) (dist (.conj A B) .top E))]
  have hs : comp (comp (assocR .conj A B (.disj .top E)) (dist (.conj A B) .top E))
      (tensor .disj (assocL .conj A B .top) (id E)) =
      comp (tensor .conj (id A) (dist B .top E)) (dist A (.conj B .top) E) := by
    simpa only [Laws.assoc] using (CutDistribution.conjunction A B .top E).symm
  rw [hs]
  simp only [Laws.assoc]
  rw [← Laws.dist_nat (id A) (fst B .top) (id E)]

theorem mix_distribution (T C D E : NormalForm P) :
    comp (tensor .conj (id T) (mix (.disj C D) E))
      (comp (tensor .conj (id T) (assocL .disj C D E)) (dist T C (.disj D E))) =
      comp (assocR .conj T (.disj C D) E)
        (comp (tensor .conj (dist T C D) (id E))
          (comp (mix (.disj (.conj T C) D) E) (assocL .disj (.conj T C) D E))) := by
  rw [CutDistribution.disjunction]
  rw [← Laws.assoc (tensor .conj (id T) (mix (.disj C D) E)),← mix_strength]
  simp only [Laws.assoc]
  rw [← Laws.assoc (mix (.conj T (.disj C D)) E),Laws.mix_nat]
  rw [Laws.assoc]

/-- The contextual cut/mix equation before context-fold comparisons. -/
theorem splice_mix {T C D E X Y Z : NormalForm P}
    (f : Hom X (.disj C D)) (g : Hom Y E) (h : Hom (.conj C T) Z) :
    splice (comp (tensor .conj f g) (comp (mix (.disj C D) E) (assocL .disj C D E))) h =
      comp (assocR .conj T X Y)
        (comp (tensor .conj (splice f h) g)
          (comp (mix (.disj Z D) E) (assocL .disj Z D E))) := by
  rw [Splice.input]
  unfold splice
  rw [tensor_factor .conj (id T) (mix (.disj C D) E) (assocL .disj C D E)]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id T) (mix (.disj C D) E)),
    ← Laws.assoc (comp (tensor .conj (id T) (mix (.disj C D) E))
      (tensor .conj (id T) (assocL .disj C D E)))]
  have hd : comp (comp (tensor .conj (id T) (mix (.disj C D) E))
      (tensor .conj (id T) (assocL .disj C D E))) (dist T C (.disj D E)) =
      comp (assocR .conj T (.disj C D) E)
        (comp (tensor .conj (dist T C D) (id E))
          (comp (mix (.disj (.conj T C) D) E) (assocL .disj (.conj T C) D E))) := by
    simpa only [Laws.assoc] using mix_distribution T C D E
  rw [hd]
  simp only [Laws.assoc]
  have ho : comp (assocL .disj (.conj T C) D E)
      (tensor .disj (comp (swap .conj T C) h) (id (.disj D E))) =
      comp (tensor .disj (tensor .disj (comp (swap .conj T C) h) (id D)) (id E))
        (assocL .disj Z D E) := by
    simpa only [Laws.tensor_id] using
      Laws.assocL_nat .disj (comp (swap .conj T C) h) (id D) (id E)
  rw [ho]
  rw [← Laws.assoc (mix (.disj (.conj T C) D) E),Laws.mix_nat]
  simp only [Laws.assoc]
  have hn : comp (tensor .conj (id T) (tensor .conj f g))
      (assocR .conj T (.disj C D) E) =
      comp (assocR .conj T X Y) (tensor .conj (tensor .conj (id T) f) g) := by
    simpa only [Laws.tensor_id] using (Laws.assocR_nat .conj (id T) f g).symm
  rw [← Laws.assoc (tensor .conj (id T) (tensor .conj f g)),hn]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (dist T C D) (id E)),Laws.tensor_comp,Laws.comp_id]
  rw [← Laws.assoc (tensor .conj (tensor .conj (id T) f) g),Laws.tensor_comp,Laws.comp_id]

end BinaryMix
end DosenPetric.Reduced.Gentzen
