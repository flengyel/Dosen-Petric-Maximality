module

public import DosenPetric.GentzenRightContractionCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.ContractionSplice
universe u
variable {P : Type u}

theorem reflected_input_head {R C V Y Z : NormalForm P}
    (h : Hom (.conj C R) Z) (f : Hom V (.disj Y C)) :
    PrincipalDisjunction.reflectedSplice (comp (swap .conj R C) h) f =
      splice (comp f (swap .disj Y C)) h := by
  unfold PrincipalDisjunction.reflectedSplice
  rw [← Laws.assoc (swap .conj C R),Laws.swap_swap,Laws.id_comp]

theorem frontDoubles_merge_head (C Y : NormalForm P) :
    comp (frontDoubles C Y)
      (comp (assocL .disj Y C C)
        (comp (tensor .disj (id Y) (codiag C)) (swap .disj Y C))) =
      comp (assocR .disj C C Y) (tensor .disj (codiag C) (id Y)) := by
  have he := congrArg (fun k => comp k (swap .disj Y C)) (frontDoubles_merge C Y)
  simpa only [Laws.assoc,Laws.swap_swap,Laws.comp_id] using he

/-- A right contraction shares its original right premise across the two
    selected output copies. -/
theorem head_right_binary {R C V Y Z : NormalForm P}
    (h : Hom (.conj C R) Z) (f : Hom V (.disj C (.disj C Y))) :
    splice (comp f (comp (assocR .disj C C Y) (tensor .disj (codiag C) (id Y)))) h =
      comp (tensor .conj (diag R) (id V))
        (comp (assocL .conj R R V)
          (comp (splice (comp (splice f h) ((sideM P .disj).cross C Z Y)) h)
            (comp (assocR .disj Z Z Y) (tensor .disj (codiag Z) (id Y))))) := by
  have he := right_binary (comp (swap .conj R C) h) (comp f (frontDoubles C Y))
  rw [reflected_double_head,reflected_input_head,reflected_input_head] at he
  simp only [Laws.assoc] at he
  rw [frontDoubles_merge_head,PrincipalDisjunction.reflection_outer] at he
  exact he

end DosenPetric.Reduced.Gentzen.ContractionSplice
