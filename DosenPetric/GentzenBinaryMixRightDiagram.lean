module

public import DosenPetric.GentzenBinaryMixMirror

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryMix

theorem swap_twice (o : Op) (A B X : NormalForm P) (h : Hom (o.formula A B) X) :
    comp (swap o A B) (comp (swap o B A) h) = h := by
  rw [← Laws.assoc,Laws.swap_swap,Laws.id_comp]

/-- The right-premise cut/mix diagram, interpreted in the actual Reduced category. -/
theorem splice_mix_right {T C D E X Y Z : NormalForm P}
    (f : Hom X (.disj C D)) (g : Hom Y E) (h : Hom (.conj C T) Z) :
    splice f (comp ((sideM P .conj).cross C Y T)
      (comp (tensor .conj g h) (mix E Z))) =
      comp (assocL .conj Y T X)
        (comp (tensor .conj g (splice f h))
          (comp (mix E (.disj Z D)) (assocR .disj E Z D))) := by
  have hm₀ := @MirrorCalculus.BinaryMix.splice_mix P
    (mirror D) (mirror C) (mirror T) (mirror Y) (mirror Z) (mirror E) (mirror X)
  simp only [MirrorInterpretation.splice_native,MirrorCalculus.Hom,MirrorCalculus.comp,
    MirrorCalculus.tensor,MirrorCalculus.assocL,MirrorCalculus.assocR,MirrorCalculus.mix,
    mirror] at hm₀
  repeat rw [mirror_involutive] at hm₀
  have hm := hm₀ (comp (swap .conj T C) h) g (comp f (swap .disj C D))
  simp only [Laws.assoc,Laws.swap_swap,Laws.comp_id,swap_twice] at hm
  rw [Laws.mix_nat] at hm
  rw [← Laws.assoc (mix Y (.conj T X)),Laws.mix_nat] at hm
  have ht : tensor .conj g (comp (swap .conj T C) h) =
      comp (tensor .conj (id Y) (swap .conj T C)) (tensor .conj g h) := by
    rw [Laws.tensor_comp,Laws.id_comp]
  rw [ht] at hm
  have hr : comp (swap .conj C (.conj Y T))
      (comp (assocL .conj Y T C) (tensor .conj (id Y) (swap .conj T C))) =
      (sideM P .conj).cross C Y T :=
    (conjDiagonal P).dual_outer_route (rightOut_assocR .conj) (side_swap_snd .conj) Y C T
  simp only [Laws.assoc] at hm
  rw [← Laws.assoc (assocL .conj Y T C),
    ← Laws.assoc (swap .conj C (.conj Y T)),hr] at hm
  exact hm

end BinaryMix
end DosenPetric.Reduced.Gentzen
