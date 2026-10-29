module

public import DosenPetric.GentzenMirrorMixedSymmetry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

theorem sourceConj_swap (X Y A B : NormalForm P) :
    ofTerm (Rules.sourceConj X Y A B) =
      comp (tensor .conj (swap .conj X Y) (swap .disj A B))
        (comp (ofTerm (Rules.sourceConj Y X B A))
          (swap .disj (.conj Y B) (.conj X A))) := by
  obtain ⟨X,rfl⟩ : ∃ X' : NormalForm P, mirror X' = X := ⟨mirror X,mirror_involutive X⟩
  obtain ⟨Y,rfl⟩ : ∃ Y' : NormalForm P, mirror Y' = Y := ⟨mirror Y,mirror_involutive Y⟩
  obtain ⟨A,rfl⟩ : ∃ A' : NormalForm P, mirror A' = A := ⟨mirror A,mirror_involutive A⟩
  obtain ⟨B,rfl⟩ : ∃ B' : NormalForm P, mirror B' = B := ⟨mirror B,mirror_involutive B⟩
  have he := MirrorCalculus.BinaryLogical.mixedDisj_swap B Y A X
  simpa only [MirrorInterpretation.mixed_source,MirrorCalculus.comp,MirrorCalculus.tensor,
    MirrorCalculus.swap,mirror,Laws.assoc] using he


theorem disjPair_swap {A B X Y U V : NormalForm P}
    (f : Hom (.conj A X) U) (g : Hom (.conj B Y) V) :
    disjPair f g =
      comp (tensor .conj (swap .disj A B) (swap .conj X Y))
        (comp (disjPair g f) (swap .disj V U)) := by
  unfold disjPair
  rw [sourceConj_swap X Y A B]
  simp only [Laws.assoc]
  rw [Laws.swap_nat .disj (comp (swap .conj Y B) g) (comp (swap .conj X A) f)]
  have hi := Laws.swap_nat .conj (swap .disj A B) (swap .conj X Y)
  rw [← Laws.assoc (tensor .conj (swap .disj A B) (swap .conj X Y)),← hi]
  simp only [Laws.assoc]

end DisjLogical
end DosenPetric.Reduced.Gentzen
