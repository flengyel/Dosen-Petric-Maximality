module
import DosenPetric.GentzenBlockedLeftDisjCore
import DosenPetric.GentzenSplitPairs
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
open BlockedLeftDisj
universe u
example {P : Type u} (C F H A B R : NormalForm P) :
    comp (kernel (.conj (.conj F H) (.disj A B)) C R)
      (tensor .disj (parent C F H A B) (id R)) = reconstruction C F H A B R := by
  apply (((SplitPair.product C (.conj F A)).sumLeft (.conj C (.conj H B))).sumLeft R).ext
  all_goals simp only [SplitPair.sumLeft,SplitPair.product]
