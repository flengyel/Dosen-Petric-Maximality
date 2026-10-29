module

public import DosenPetric.GentzenMirrorMixedSymmetry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
namespace DosenPetric.Reduced.Gentzen.MirrorCalculus
variable {P : Type u}
namespace BinaryLogical

def exchangeCore (o : Op) (X Y Z : NormalForm P) :
    Hom (o.formula (o.formula X Y) Z) (o.formula (o.formula X Z) Y) :=
  comp (assocL o X Y Z) (comp (tensor o (id X) (swap o Y Z)) (assocR o X Z Y))

theorem mixedDisj_nat {A D B E A' D' B' E' : NormalForm P}
    (a : Hom A A') (d : Hom D D') (b : Hom B B') (e : Hom E E') :
    comp (mixedDisj A D B E) (tensor .disj (tensor .conj a b) (tensor .disj d e)) =
      comp (tensor .conj (tensor .disj a d) (tensor .disj b e)) (mixedDisj A' D' B' E') := by
  simpa only [MirrorInterpretation.mixed_source,comp,tensor,mirror] using
    (sourceConj_nat e d b a).symm

def residualOutput (Q D R E : NormalForm P) :
    Hom (.disj Q (.disj (.disj D R) E)) (.disj (.disj Q (.disj D E)) R) :=
  comp (tensor .disj (id Q) (exchangeCore .disj D R E))
    (assocR .disj Q (.disj D E) R)

theorem residual_finish (K Q D E R : NormalForm P) (s : Hom K Q) :
    comp (assocL .disj K (.disj E D) R)
      (comp (tensor .disj (id K) (assocL .disj E D R))
        (comp (tensor .disj s (swap .disj E (.disj D R))) (residualOutput Q D R E))) =
      tensor .disj (tensor .disj s (swap .disj E D)) (id R) := by
  dsimp only [residualOutput,exchangeCore,comp,tensor,assocL,assocR,swap,id,mirror]
  simp only [Gentzen.ProductCalculation.assocR_pair,Gentzen.ProductCalculation.assocL_pair,
    Gentzen.ProductCalculation.swap_pair,Gentzen.ProductCalculation.tensor_pair,
    Gentzen.ProductCalculation.pair_pre,Gentzen.ProductCalculation.pair_fst,
    Gentzen.ProductCalculation.pair_snd,Gentzen.ProductCalculation.pair_fst_comp,
    Gentzen.ProductCalculation.pair_snd_comp,Reduced.Laws.comp_id,Reduced.Laws.assoc]

/-- The residual output comparison when cut meets the first logical factor. -/
theorem mixed_first_residual (A D B E R : NormalForm P) :
    comp (innerDisj (.disj A D) R (.disj B E))
      (tensor .disj (mixedDisj A D B E) (id R)) =
      comp (tensor .conj (assocL .disj A D R) (id (.disj B E)))
        (comp (mixedDisj A (.disj D R) B E)
          (residualOutput (.conj A B) D R E)) := by
  have hs : comp (swap .conj (.disj B E) (.disj A D))
      (mixedDisj A D B E) =
      comp (mixedDisj B E A D)
        (tensor .disj (swap .conj B A) (swap .disj E D)) := by
    rw [mixedDisj_swap A D B E]
    rw [← Laws.assoc,Laws.swap_swap,Laws.id_comp]
  rw [innerDisj,CutDistribution.step]
  simp only [Laws.assoc]
  rw [Laws.tensor_comp,hs,Laws.id_comp]
  have ht : tensor .disj (comp (mixedDisj B E A D)
      (tensor .disj (swap .conj B A) (swap .disj E D))) (id R) =
      comp (tensor .disj (mixedDisj B E A D) (id R))
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
end DosenPetric.Reduced.Gentzen.MirrorCalculus
