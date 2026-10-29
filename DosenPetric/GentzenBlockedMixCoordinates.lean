module

public import DosenPetric.GentzenBlockedMixRoutes

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedMix
universe u
variable {P : Type u}

/-- The duplication program agrees with the product comparison on both sides. -/
theorem input_square (o : Op) {Y F H : List (NormalForm P)}
    (p : Route Y F) (q : Route Y H) (I : List (NormalForm P)) :
    (side P o).comp ((inputRoute p q I).sideArrow o)
      ((side P o).comp (split o (H++I) (F++I))
        ((sideM P o).tensor (split o H I) (split o F I))) =
      (side P o).comp (split o Y I)
        ((sideD P o).pair
          ((sideM P o).tensor (q.sideArrow o) ((side P o).id (fold o I)))
          ((sideM P o).tensor (p.sideArrow o) ((side P o).id (fold o I)))) := by
  let C := side P o
  let D := sideD P o
  rw [inputRoute,← C.assoc,Route.append_split]
  apply D.ext
  · rw [C.assoc,← D.fst_nat,← C.assoc,D.pair_fst,
      C.assoc,D.pair_fst,Route.parallel_split,Route.identity_arrow]
  · rw [C.assoc,← D.snd_nat,← C.assoc,D.pair_snd,
      C.assoc,D.pair_snd,Route.parallel_split,Route.identity_arrow]

/-- Native context folds in the input comparison. -/
theorem input_square_conj {Y F H : List (NormalForm P)}
    (p : Route Y F) (q : Route Y H) (I : List (NormalForm P)) :
    comp ((inputRoute p q I).sideArrow .conj)
      (comp (ofTerm (append .conj (H++I) (F++I)).invTerm)
        (tensor .conj (ofTerm (append .conj H I).invTerm)
          (ofTerm (append .conj F I).invTerm))) =
      comp (ofTerm (append .conj Y I).invTerm)
        (sharedInput (p.sideArrow .conj) (q.sideArrow .conj)) :=
  input_square .conj p q I

theorem copair_post {A B X Y : NormalForm P} (f : Hom A X) (g : Hom B X)
    (k : Hom X Y) : comp (copair f g) k = copair (comp f k) (comp g k) :=
  (disjDiagonal P).pair_pre k f g

/-- The duplicated residual block is identified after the native mix. -/
theorem output_square (D E R : List (NormalForm P)) :
    comp (tensor .disj (ofTerm (append .disj E R).toTerm)
      (ofTerm (append .disj D R).toTerm))
      (comp (ofTerm (append .disj (E++R) (D++R)).toTerm)
        ((outputRoute D E R).sideArrow .disj)) =
      comp (sharedOutput (succ E) (succ D) (succ R))
        (comp (tensor .disj (ofTerm (append .disj E D).toTerm) (id (succ R)))
          (ofTerm (append .disj (E++D) R).toTerm)) := by
  have he := input_square .disj (Route.takeSecond E D) (Route.takeFirst E D) R
  rw [Route.takeFirst_arrow,Route.takeSecond_arrow] at he
  dsimp only [side,sideM,sideD,disjMonoidal,opposite,category,split,
    DiagonalData.pair,disjDiagonal] at he
  change _ = comp
    (copair
      (tensor .disj (comp (inl (succ E) (succ D)) (ofTerm (append .disj E D).toTerm)) (id (succ R)))
      (tensor .disj (comp (inr (succ E) (succ D)) (ofTerm (append .disj E D).toTerm)) (id (succ R))))
    (ofTerm (append .disj (E++D) R).toTerm) at he
  change comp (comp (tensor .disj (ofTerm (append .disj E R).toTerm)
      (ofTerm (append .disj D R).toTerm))
      (ofTerm (append .disj (E++R) (D++R)).toTerm))
      ((outputRoute D E R).sideArrow .disj) = _ at he
  rw [Laws.assoc] at he
  rw [he]
  unfold sharedOutput
  have ht {V : NormalForm P} (a : Hom V (.disj (succ E) (succ D))) :
      tensor .disj (comp a (ofTerm (append .disj E D).toTerm)) (id (succ R)) =
        comp (tensor .disj a (id (succ R)))
          (tensor .disj (ofTerm (append .disj E D).toTerm) (id (succ R))) := by
    rw [Laws.tensor_comp,Laws.id_comp]
  rw [ht,ht]
  simp only [copair_post,Laws.assoc]

end DosenPetric.Reduced.Gentzen.BlockedMix
