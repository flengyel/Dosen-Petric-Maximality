module

public import DosenPetric.GentzenBlockedLeftGammaDisjRank

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.PrincipalDisjunction
universe u
variable {P : Type u}

theorem reflected_selected {C C' R X Y Z : NormalForm P} (k : Hom C C')
    (g : Hom X (.disj Y C)) (h : Hom (.conj R C') Z) :
    reflectedSplice h (comp g (tensor .disj (id Y) k)) =
      reflectedSplice (comp (tensor .conj (id R) k) h) g := by
  have ho := Laws.swap_nat .disj (id Y) k
  have hi := Laws.swap_nat .conj k (id R)
  unfold reflectedSplice
  rw [Laws.assoc g,← ho]
  rw [← Laws.assoc (swap .conj C R),hi,Laws.assoc,Splice.selected]
  simp only [Laws.assoc]

theorem reflected_context {R R' C X Y Z : NormalForm P} (k : Hom R' R)
    (g : Hom X (.disj Y C)) (h : Hom (.conj R C) Z) :
    reflectedSplice (comp (tensor .conj k (id C)) h) g =
      comp (tensor .conj k (id X)) (reflectedSplice h g) := by
  unfold reflectedSplice
  rw [← Laws.assoc (swap .conj C R'),Laws.swap_nat,Laws.assoc,Splice.context]

theorem reflected_output {R C X Y Z Z' : NormalForm P} (k : Hom Z Z')
    (g : Hom X (.disj Y C)) (h : Hom (.conj R C) Z) :
    reflectedSplice (comp h k) g =
      comp (reflectedSplice h g) (tensor .disj k (id Y)) := by
  unfold reflectedSplice
  rw [← Laws.assoc,Splice.output]

end DosenPetric.Reduced.Gentzen.PrincipalDisjunction
