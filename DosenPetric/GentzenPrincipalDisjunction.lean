module

public import DosenPetric.GentzenHeadRouting

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PrincipalDisjunction

/-- A splice in the reflected presentation, written as an actual cut splice. -/
def reflectedSplice {D C X Z Y : NormalForm P}
    (f : Hom (.conj D C) X) (g : Hom Z (.disj Y C)) : Hom (.conj D Z) (.disj X Y) :=
  splice (comp g (swap .disj Y C)) (comp (swap .conj C D) f)

theorem reflected_splice {X Y C D Z : NormalForm P}
    (f : MirrorCalculus.Hom X (.disj C D)) (g : MirrorCalculus.Hom (.conj C Y) Z) :
    MirrorCalculus.splice f g = reflectedSplice f g := MirrorInterpretation.splice_native f g

/-- The dual principal equation in the original quotient category. -/
theorem reflected_equation {T A B D E V X Y : NormalForm P}
    (f : Hom (.conj D A) X) (g : Hom (.conj E B) Y)
    (h : Hom V (.disj (.disj T B) A)) :
    reflectedSplice
        (comp (ofTerm (Rules.sourceConj E D B A)) (tensor .disj g f))
        (comp h (assocL .disj T B A)) =
      comp (assocL .conj E D V)
        (comp (reflectedSplice g
          (comp (reflectedSplice f h) (assocR .disj X T B))) (assocR .disj Y X T)) := by
  have hm := @MirrorCalculus.PrincipalConjunction.equation P
    (mirror T) (mirror A) (mirror B) (mirror D) (mirror E)
    (mirror V) (mirror X) (mirror Y)
  simp only [reflected_splice, MirrorInterpretation.mixed_source,
    MirrorCalculus.Hom, MirrorCalculus.comp, MirrorCalculus.tensor,
    MirrorCalculus.assocL, MirrorCalculus.assocR, mirror] at hm
  repeat rw [mirror_involutive] at hm
  simpa only [Laws.assoc] using hm f g h

end PrincipalDisjunction
end DosenPetric.Reduced.Gentzen
