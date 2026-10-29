module

public import DosenPetric.GentzenBlockedRightConjCanonical

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedRightConj
universe u
variable {P : Type u}

def sharedOutput {D E U : NormalForm P} (Z Q : NormalForm P) (p : Hom D U) (q : Hom E U) :
    Hom (.disj Q (.disj (.disj Z D) (.disj Z E))) (.disj Z (.disj Q U)) :=
  comp (tensor .disj (id Q) (copair (tensor .disj (id Z) p) (tensor .disj (id Z) q)))
    ((sideM P .disj).cross Z Q U)

theorem cross_residual {U V : NormalForm P} (k : Hom U V) (Z Q : NormalForm P) :
    comp ((sideM P .disj).cross Z Q U) (tensor .disj (id Z) (tensor .disj (id Q) k)) =
      comp (tensor .disj (id Q) (tensor .disj (id Z) k)) ((sideM P .disj).cross Z Q V) := by
  have he := (sideM P .disj).cross_nat (id Z) (id Q) k
  dsimp only [sideM,side,disjMonoidal,opposite,category] at he ⊢
  exact he.symm

theorem merge_routes {D E U : NormalForm P} (Z Q : NormalForm P) (p : Hom D U) (q : Hom E U) :
    comp (DoubleConjSplice.mergeOutput Z Q D E)
      (tensor .disj (id Z) (tensor .disj (id Q) (copair p q))) = sharedOutput Z Q p q := by
  rw [DoubleConjSplice.mergeOutput,Laws.assoc,cross_residual,← Laws.assoc,Laws.tensor_comp,
    Laws.id_comp,BlockedMix.copair_post]
  simp only [Laws.tensor_comp,Laws.id_comp]
  have hp := (disjDiagonal P).pair_fst p q
  have hq := (disjDiagonal P).pair_snd p q
  change comp (inl D E) (copair p q) = p at hp
  change comp (inr D E) (copair p q) = q at hq
  rw [hp,hq]
  rfl

def sharedParent {A B C D E U X Y : NormalForm P} (p : Hom D U) (q : Hom E U)
    (f : Hom X (.disj A (.disj C D))) (g : Hom Y (.disj B (.disj C E))) :
    Hom (.conj X Y) (.disj C (.disj (.conj A B) U)) :=
  comp (tensor .conj f g)
    (comp (ofTerm (Term.mixedDisj A (.disj C D) B (.disj C E))) (sharedOutput C (.conj A B) p q))

theorem shared_equation {A B C D E U R X Y Z : NormalForm P} (p : Hom D U) (q : Hom E U)
    (f : Hom X (.disj A (.disj C D))) (g : Hom Y (.disj B (.disj C E)))
    (h : Hom (.conj C R) Z) :
    splice (sharedParent p q f g) h =
      comp (BlockedMix.rightSharedInput R X Y)
        (comp (tensor .conj (DoubleConjSplice.child f h) (DoubleConjSplice.child g h))
          (comp (ofTerm (Term.mixedDisj A (.disj Z D) B (.disj Z E)))
            (sharedOutput Z (.conj A B) p q))) := by
  have he := congrArg (fun k => comp k
    (tensor .disj (id Z) (tensor .disj (id (.conj A B)) (copair p q)))) (canonical_equation f g h)
  rw [← Splice.residual] at he
  simp only [parent,Laws.assoc] at he
  rw [merge_routes,merge_routes] at he
  exact he

end DosenPetric.Reduced.Gentzen.BlockedRightConj
