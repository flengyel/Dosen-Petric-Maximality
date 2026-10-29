module

public import DosenPetric.GentzenBlockedMixCore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedMix
universe u
variable {P : Type u}

/-- Duplicate the unchanged right-premise context for the two original cuts. -/
def rightSharedInput (T B A : NormalForm P) :
    Hom (.conj T (.conj B A)) (.conj (.conj T B) (.conj T A)) :=
  pair (tensor .conj (id T) (fst B A)) (tensor .conj (id T) (snd B A))

/-- Retain both original residual blocks and identify their common new output. -/
def rightSharedOutput {F H Y Z : NormalForm P} (p : Hom F Y) (q : Hom H Y) :
    Hom (.disj (.disj Z H) (.disj Z F)) (.disj Z Y) :=
  copair (tensor .disj (id Z) q) (tensor .disj (id Z) p)

/-- The two selected child outputs are identified before the original cut. -/
def rightSharedParent {C F H Y A B : NormalForm P} (p : Hom F Y) (q : Hom H Y)
    (f : Hom A (.disj C F)) (g : Hom B (.disj C H)) :
    Hom (.conj B A) (.disj C Y) :=
  comp (tensor .conj g f) (comp (mix (.disj C H) (.disj C F)) (rightSharedOutput p q))

/-- The two smaller cuts have the unchanged original right premise. -/
theorem right_shared_splice {C F H Y A B T Z : NormalForm P}
    (p : Hom F Y) (q : Hom H Y) (f : Hom A (.disj C F)) (g : Hom B (.disj C H))
    (h : Hom (.conj C T) Z) :
    splice (rightSharedParent p q f g) h =
      comp (rightSharedInput T B A)
        (comp (tensor .conj (splice g h) (splice f h))
          (comp (mix (.disj Z H) (.disj Z F)) (rightSharedOutput p q))) := by
  unfold rightSharedParent
  rw [← Laws.assoc,mix_paths,union_post]
  unfold rightSharedOutput
  have hl {V W K : NormalForm P} (a : Hom V K) (b : Hom W K) :
      comp (inl V W) (copair a b) = a := (disjDiagonal P).pair_fst a b
  have hr {V W K : NormalForm P} (a : Hom V K) (b : Hom W K) :
      comp (inr V W) (copair a b) = b := (disjDiagonal P).pair_snd a b
  simp only [Laws.assoc]
  rw [hl,hr,MixCalculation.splice_union_left]
  have hs {V W S : NormalForm P} (a : Hom V W) (b : Hom W (.disj C S)) (k : Hom S Y) :
      splice (comp a (comp b (tensor .disj (id C) k))) h =
        comp (tensor .conj (id T) a) (comp (splice b h) (tensor .disj (id Z) k)) := by
    rw [← Laws.assoc,Splice.residual,Splice.input,Laws.assoc]
  rw [hs,hs]
  rw [← Laws.assoc (tensor .conj (splice g h) (splice f h)),mix_paths]
  simp only [union_pre,union_post,Laws.assoc]
  unfold rightSharedInput
  simp only [← Laws.assoc,ProductCalculation.pair_fst,ProductCalculation.pair_snd]
  simp only [Laws.assoc]
  rw [hl,hr]

end DosenPetric.Reduced.Gentzen.BlockedMix
