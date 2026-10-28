module

public import DosenPetric.GentzenConjFirstSplice

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric
universe u v
namespace DiagonalData
variable {O : Type u} {C : Category.{u,v} O} {M : MonoidalData C} (D : DiagonalData M)
variable (hu : ∀ A B, C.comp (M.assocR A B M.unit) (M.rightOut (M.obj A B)) =
  M.tensor (C.id A) (M.rightOut B))
variable (hs : ∀ A B, C.comp (M.swap A B) (D.snd B A) = D.fst A B)

include hu hs in
theorem first_residual (K Q T E R : O) (s : C.Hom Q K) :
    C.comp (M.assocL Q (M.obj T E) R)
      (C.comp (M.tensor (C.id Q)
        (C.comp (M.assocL T E R)
          (C.comp (M.tensor (C.id T) (M.swap E R)) (M.assocR T R E))))
        (C.comp (M.tensor s (M.swap (M.obj T R) E))
          (C.comp (M.tensor (C.id K) (M.assocR E T R)) (M.assocR K (M.obj E T) R)))) =
      M.tensor (M.tensor s (M.swap T E)) (C.id R) := by
  simp only [D.assocR_pair hu,D.assocL_pair hu,D.swap_pair hs,D.tensor_pair,D.pair_pre,
    D.pair_fst,D.pair_snd,D.pair_fst_comp,D.pair_snd_comp,C.comp_id,C.assoc]

end DiagonalData
namespace Reduced.Gentzen
variable {P : Type u}
namespace BinaryLogical

def residualOutput (Q D R E : NormalForm P) :
    Hom (.disj Q (.disj (.disj D R) E)) (.disj (.disj Q (.disj D E)) R) :=
  comp (tensor .disj (id Q) (exchangeCore .disj D R E))
    (assocR .disj Q (.disj D E) R)

theorem residual_finish (K Q D E R : NormalForm P) (s : Hom K Q) :
    comp (assocL .disj K (.disj E D) R)
      (comp (tensor .disj (id K) (assocL .disj E D R))
        (comp (tensor .disj s (swap .disj E (.disj D R))) (residualOutput Q D R E))) =
      tensor .disj (tensor .disj s (swap .disj E D)) (id R) := by
  have he := (disjDiagonal P).first_residual (rightIn_assocL .disj)
    (side_swap_snd .disj) K Q D E R s
  dsimp only [disjMonoidal,opposite,category] at he
  simpa only [residualOutput,exchangeCore,Laws.assoc] using he

/-- The residual output comparison when cut meets the first logical factor. -/
theorem mixed_first_residual (A D B E R : NormalForm P) :
    comp (innerDisj (.disj A D) R (.disj B E))
      (tensor .disj (ofTerm (Term.mixedDisj A D B E)) (id R)) =
      comp (tensor .conj (assocL .disj A D R) (id (.disj B E)))
        (comp (ofTerm (Term.mixedDisj A (.disj D R) B E))
          (residualOutput (.conj A B) D R E)) := by
  have hs : comp (swap .conj (.disj B E) (.disj A D))
      (ofTerm (Term.mixedDisj A D B E)) =
      comp (ofTerm (Term.mixedDisj B E A D))
        (tensor .disj (swap .conj B A) (swap .disj E D)) := by
    rw [mixedDisj_swap A D B E]
    rw [← Laws.assoc,Laws.swap_swap,Laws.id_comp]
  rw [innerDisj]
  simp only [Laws.assoc]
  rw [Laws.tensor_comp,hs,Laws.id_comp]
  have ht : tensor .disj (comp (ofTerm (Term.mixedDisj B E A D))
      (tensor .disj (swap .conj B A) (swap .disj E D))) (id R) =
      comp (tensor .disj (ofTerm (Term.mixedDisj B E A D)) (id R))
        (tensor .disj (tensor .disj (swap .conj B A) (swap .disj E D)) (id R)) := by
    rw [Laws.tensor_comp,Laws.id_comp]
  rw [ht,mixedDisj_swap A (.disj D R) B E]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (assocL .disj A D R) (id (.disj B E))),← Laws.swap_nat]
  have he := congrArg (fun k => comp (swap .conj (.disj (.disj A D) R) (.disj B E))
    (comp k (comp (tensor .disj (swap .conj B A) (swap .disj E (.disj D R)))
      (residualOutput (.conj A B) D R E)))) (mixed_residual B E A D R)
  simp only [Laws.assoc] at he ⊢
  rw [residual_finish] at he
  exact he

end BinaryLogical
end Reduced.Gentzen
end DosenPetric
