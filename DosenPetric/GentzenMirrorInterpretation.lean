module

public import DosenPetric.GentzenMirrorPrincipalEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace MirrorInterpretation

/-- The reflected mixed comparison is the actual source conjunction comparison. -/
theorem mixed_source (A D B E : NormalForm P) :
    MirrorCalculus.mixedDisj A D B E =
      ofTerm (Rules.sourceConj (mirror E) (mirror D) (mirror B) (mirror A)) := by
  dsimp only [MirrorCalculus.mixedDisj, MirrorCalculus.comp, MirrorCalculus.tensor,
    MirrorCalculus.dist, MirrorCalculus.swap, MirrorCalculus.assocL, MirrorCalculus.id, mirror]
  simp only [Rules.sourceConj, ofTerm_comp, ofTerm_tensor, ofTerm_id,
    term_swap, term_dist, term_assocL, Laws.assoc]
  rw [tensor_factor .conj (id (mirror E))
      (tensor .conj (id (mirror D)) (swap .disj (mirror B) (mirror A))),
    tensor_factor .conj (id (mirror E)) (dist (mirror D) (mirror A) (mirror B))]
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocL .conj (mirror E) (mirror D) (.disj (mirror B) (mirror A))),
    Laws.assocL_nat, Laws.tensor_id]
  simp only [Laws.assoc]

/-- A mirrored splice is an actual cut splice with its selected slots exchanged. -/
theorem splice_native {X Y C D Z : NormalForm P}
    (f : MirrorCalculus.Hom X (.disj C D)) (g : MirrorCalculus.Hom (.conj C Y) Z) :
    MirrorCalculus.splice f g =
      splice (comp g (swap .disj (mirror Y) (mirror C)))
        (comp (swap .conj (mirror C) (mirror D)) f) := by
  dsimp only [MirrorCalculus.splice, MirrorCalculus.comp, MirrorCalculus.tensor,
    MirrorCalculus.dist, MirrorCalculus.swap, MirrorCalculus.id, mirror]
  unfold splice
  simp only [Laws.assoc]
  rw [← Laws.assoc (swap .conj (mirror D) (mirror C)), Laws.swap_swap, Laws.id_comp]

end MirrorInterpretation
end DosenPetric.Reduced.Gentzen
