module

public import DosenPetric.GentzenMirrorSelectedCore
public import DosenPetric.GentzenDisjSecondSelected

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

def selectedSource (X Y A B C : NormalForm P) :
    Hom (.conj (.conj (.conj X Y) (.disj A B)) C)
      (.disj (.conj X A) (.conj (.conj Y C) B)) :=
  comp (BinaryLogical.exchangeCore .conj (.conj X Y) (.disj A B) C)
    (comp (tensor .conj (assocL .conj X Y C) (id (.disj A B)))
      (ofTerm (Rules.sourceConj X (.conj Y C) A B)))

theorem reflected_coCross (A B E : NormalForm P) :
    MirrorCalculus.BinaryLogical.coCross A B E =
      BinaryLogical.exchangeCore .conj (mirror E) (mirror B) (mirror A) := by
  simp only [MirrorCalculus.BinaryLogical.coCross,MirrorCalculus.BinaryLogical.cross,
    MirrorCalculus.comp,MirrorCalculus.tensor,MirrorCalculus.assocL,MirrorCalculus.assocR,
    MirrorCalculus.swap,MirrorCalculus.id,BinaryLogical.exchangeCore,mirror,Laws.assoc]

theorem reflected_selected (A C D B E : NormalForm P) :
    MirrorCalculus.BinaryLogical.selectedMixed A C D B E =
      selectedSource (mirror E) (mirror D) (mirror B) (mirror A) (mirror C) := by
  simp only [MirrorCalculus.BinaryLogical.selectedMixed,MirrorInterpretation.mixed_source,
    reflected_coCross,MirrorCalculus.comp,MirrorCalculus.tensor,MirrorCalculus.assocL,
    MirrorCalculus.id,mirror,selectedSource,Laws.assoc]

theorem reflected_selected_core {A B X Y C R U V W : NormalForm P}
    (f : Hom (.conj X A) U) (g : Hom (.conj (.conj Y C) B) V) (h : Hom W (.disj R C)) :
    PrincipalDisjunction.reflectedSplice
      (comp (selectedSource X Y A B C) (tensor .disj f g)) h =
      comp (selectedSource X Y A B W)
        (comp (tensor .disj f
          (comp (BinaryLogical.exchangeCore .conj Y W B)
            (PrincipalDisjunction.reflectedSplice
              (comp (BinaryLogical.exchangeCore .conj Y B C) g) h)))
          (assocR .disj U V R)) := by
  have hm := @MirrorCalculus.BinaryLogical.conjR_left_first_core P
    (mirror B) (mirror A) (mirror C) (mirror Y) (mirror X)
    (mirror V) (mirror U) (mirror R) (mirror W)
  simp only [PrincipalDisjunction.reflected_splice,reflected_selected,reflected_coCross,
    MirrorCalculus.Hom,MirrorCalculus.comp,MirrorCalculus.tensor,MirrorCalculus.assocR,mirror] at hm
  repeat rw [mirror_involutive] at hm
  simpa only [Laws.assoc] using hm g f h

end DisjLogical
end DosenPetric.Reduced.Gentzen
