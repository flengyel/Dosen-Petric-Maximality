module

import DosenPetric.GentzenConjRightSecondSelected

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen

-- An unfinished next diagram, outside production and public type checks.
example {P : Type u} (A D B E : NormalForm P) :
    ofTerm (Term.mixedDisj A D B E) =
      comp (swap .conj (.disj A D) (.disj B E))
        (comp (ofTerm (Term.mixedDisj B E A D))
          (tensor .disj (swap .conj B A) (swap .disj E D))) := by
  rw [mixedDisj_eq,mixedDisj_eq]
  simp only [innerDisj,Laws.assoc]
