module

public import DosenPetric.GentzenMirrorBinaryCore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

theorem reflected_cross (C X Y : NormalForm P) :
    MirrorCalculus.BinaryLogical.cross .conj C X Y =
      BinaryLogical.exchangeCore .disj (mirror Y) (mirror C) (mirror X) := by
  simp only [MirrorCalculus.BinaryLogical.cross,MirrorCalculus.comp,MirrorCalculus.tensor,
    MirrorCalculus.assocL,MirrorCalculus.assocR,MirrorCalculus.swap,MirrorCalculus.id,
    BinaryLogical.exchangeCore,mirror,Laws.assoc]

theorem reflected_core {A D B E C Z X Y W : NormalForm P}
    (f : Hom (.conj D A) X) (g : Hom (.conj E B) (.disj Y C)) (h : Hom (.conj Z C) W) :
    comp (tensor .conj (assocL .conj Z E D) (id (.disj B A)))
      (comp (assocL .conj Z (.conj E D) (.disj B A))
        (PrincipalDisjunction.reflectedSplice h
          (comp (ofTerm (Rules.sourceConj E D B A))
            (comp (tensor .disj g f) (BinaryLogical.exchangeCore .disj Y C X))))) =
      comp (ofTerm (Rules.sourceConj (.conj Z E) D B A))
        (comp (tensor .disj
          (comp (assocL .conj Z E B) (PrincipalDisjunction.reflectedSplice h g)) f)
          (assocL .disj W Y X)) := by
  have hm := @MirrorCalculus.BinaryLogical.conjR_right_second_core P
    (mirror A) (mirror D) (mirror B) (mirror E) (mirror C) (mirror Z)
    (mirror X) (mirror Y) (mirror W)
  simp only [PrincipalDisjunction.reflected_splice,MirrorInterpretation.mixed_source,
    reflected_cross,MirrorCalculus.Hom,MirrorCalculus.comp,MirrorCalculus.tensor,
    MirrorCalculus.assocL,MirrorCalculus.id,mirror] at hm
  repeat rw [mirror_involutive] at hm
  simpa only [Laws.assoc] using hm f g h

end DisjLogical
end DosenPetric.Reduced.Gentzen
