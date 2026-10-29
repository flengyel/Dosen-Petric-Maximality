module

public import DosenPetric.GentzenDisjRightCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

theorem selected_source_pair {X Y A B C U V : NormalForm P}
    (f : Hom (.conj A X) U) (g : Hom (.conj B (.conj C Y)) V) :
    comp (selectedSource X Y A B C)
      (tensor .disj (comp (swap .conj X A) f) (comp (selectedBranch Y B C) g)) =
      comp (selectedHeadInput C X Y (.disj A B))
        (comp (secondDisjInput C X Y (.disj A B)) (disjPair f g)) := by
  have hs : comp (ofTerm (Rules.sourceConj X (.conj Y C) A B))
      (tensor .disj (comp (swap .conj X A) f) (comp (selectedBranch Y B C) g)) =
      comp (swap .conj (.conj X (.conj Y C)) (.disj A B))
        (disjPair f (comp (tensor .conj (id B) (swap .conj Y C)) g)) := by
    simp only [disjPair,selectedBranch,Laws.assoc]
    rw [← Laws.assoc (swap .conj (.conj X (.conj Y C)) (.disj A B)),Laws.swap_swap,Laws.id_comp]
  simp only [selectedSource,Laws.assoc]
  rw [hs,disjPair_input_second]
  have he := congrArg (fun k => comp k (disjPair f g)) (selected_source_input X Y (.disj A B) C)
  simpa only [Laws.assoc] using he

theorem selected_parent_splice {X Y A B C R U V W : NormalForm P}
    (f : Hom (.conj A X) U) (g : Hom (.conj B (.conj C Y)) V) (h : Hom W (.disj C R)) :
    PrincipalDisjunction.reflectedSplice
      (comp (selectedSource X Y A B C)
        (tensor .disj (comp (swap .conj X A) f) (comp (selectedBranch Y B C) g)))
      (comp h (swap .disj C R)) =
      comp (tensor .conj (swap .conj (.conj X Y) (.disj A B)) (id W))
        (splice h (comp (secondDisjInput C X Y (.disj A B)) (disjPair f g))) := by
  rw [selected_source_pair,PrincipalDisjunction.reflectedSplice]
  have hh : comp (comp h (swap .disj C R)) (swap .disj R C) = h := by
    rw [Laws.assoc,Laws.swap_swap,Laws.comp_id]
  rw [hh]
  have hq : comp (swap .conj C (.conj (.conj X Y) (.disj A B)))
      (comp (selectedHeadInput C X Y (.disj A B))
        (comp (secondDisjInput C X Y (.disj A B)) (disjPair f g))) =
      comp (tensor .conj (id C) (swap .conj (.conj X Y) (.disj A B)))
        (comp (secondDisjInput C X Y (.disj A B)) (disjPair f g)) := by
    simp only [selectedHeadInput,Laws.assoc]
    rw [← Laws.assoc (swap .conj C (.conj (.conj X Y) (.disj A B))),Laws.swap_swap,Laws.id_comp]
  rw [hq,Splice.context]

theorem selected_child_splice {Y B C R V W : NormalForm P}
    (g : Hom (.conj B (.conj C Y)) V) (h : Hom W (.disj C R)) :
    PrincipalDisjunction.reflectedSplice
      (comp (BinaryLogical.exchangeCore .conj Y B C) (comp (selectedBranch Y B C) g))
      (comp h (swap .disj C R)) =
      comp (tensor .conj (swap .conj Y B) (id W))
        (splice h (comp ((sideM P .conj).cross C B Y) g)) := by
  unfold PrincipalDisjunction.reflectedSplice
  have hh : comp (comp h (swap .disj C R)) (swap .disj R C) = h := by
    rw [Laws.assoc,Laws.swap_swap,Laws.comp_id]
  rw [hh]
  have hq := congrArg (fun k => comp k g) (selected_child_head Y B C)
  simp only [Laws.assoc] at hq
  rw [hq,Splice.context]

end DisjLogical
end DosenPetric.Reduced.Gentzen
