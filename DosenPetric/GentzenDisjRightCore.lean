module

public import DosenPetric.GentzenDisjRightFactors

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

theorem disjL_right_second_core {A B X Y C R U V W : NormalForm P}
    (f : Hom (.conj A X) U) (g : Hom (.conj B (.conj C Y)) V) (h : Hom W (.disj C R)) :
    splice h (comp (secondDisjInput C X Y (.disj A B)) (disjPair f g)) =
      comp (assocL .conj (.disj A B) (.conj X Y) W)
        (comp (tensor .conj (id (.disj A B)) (assocL .conj X Y W))
          (comp (disjPair f
            (comp (assocR .conj B Y W) (splice h (comp ((sideM P .conj).cross C B Y) g))))
            (assocR .disj U V R))) := by
  let k : Hom (.conj B (.conj Y W)) (.disj V R) :=
    comp (assocR .conj B Y W) (splice h (comp ((sideM P .conj).cross C B Y) g))
  have hc : comp (BinaryLogical.exchangeCore .conj Y W B)
      (PrincipalDisjunction.reflectedSplice
        (comp (BinaryLogical.exchangeCore .conj Y B C) (comp (selectedBranch Y B C) g))
        (comp h (swap .disj C R))) =
      comp (selectedBranch Y B W) (comp (tensor .conj (id B) (swap .conj W Y)) k) := by
    rw [selected_child_splice]
    rw [← Laws.assoc (BinaryLogical.exchangeCore .conj Y W B),selected_child_result]
    simp only [k,Laws.assoc]
  have he := reflected_selected_core (comp (swap .conj X A) f)
    (comp (selectedBranch Y B C) g) (comp h (swap .disj C R))
  rw [selected_parent_splice,hc] at he
  rw [← Laws.assoc (selectedSource X Y A B W),selected_source_pair,disjPair_input_second] at he
  simp only [Laws.assoc] at he
  have hp := congrArg (fun p => comp p (comp (disjPair f k) (assocR .disj U V R)))
    (selected_parent_result X Y (.disj A B) W)
  simp only [Laws.assoc] at hp
  rw [hp] at he
  apply cancel_left _ _ (tensor .conj (swap .conj (.conj X Y) (.disj A B)) (id W))
    (tensor .conj (swap .conj (.disj A B) (.conj X Y)) (id W))
  · rw [Laws.tensor_comp,Laws.swap_swap,Laws.id_comp,Laws.tensor_id]
  · simpa only [k,Laws.assoc] using he

end DisjLogical
end DosenPetric.Reduced.Gentzen
