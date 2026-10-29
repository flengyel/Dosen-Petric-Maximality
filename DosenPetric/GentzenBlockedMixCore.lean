module

public import DosenPetric.GentzenMixUnion
public import DosenPetric.GentzenProductCalculations

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedMix
universe u
variable {P : Type u}

/-- Duplicate the unchanged input while selecting the two residual contexts. -/
def sharedInput {Y F H X : NormalForm P} (p : Hom Y F) (q : Hom Y H) :
    Hom (.conj Y X) (.conj (.conj H X) (.conj F X)) :=
  pair (tensor .conj q (id X)) (tensor .conj p (id X))

/-- Identify the two copies of the unchanged residual output. -/
def sharedOutput (E D R : NormalForm P) :
    Hom (.disj (.disj E R) (.disj D R)) (.disj (.disj E D) R) :=
  copair (tensor .disj (inl E D) (id R)) (tensor .disj (inr E D) (id R))

/-- The two right-premise branches share the selected input formula. -/
def sharedParent {C Y F H D E : NormalForm P} (p : Hom Y F) (q : Hom Y H)
    (f : Hom (.conj C F) D) (g : Hom (.conj C H) E) :
    Hom (.conj C Y) (.disj E D) :=
  comp (pair (tensor .conj (id C) q) (tensor .conj (id C) p))
    (comp (tensor .conj g f) (mix E D))

theorem mix_paths {A B D E : NormalForm P} (f : Hom A D) (g : Hom B E) :
    comp (tensor .conj g f) (mix E D) =
      union (comp (fst B A) (comp g (inl E D)))
        (comp (snd B A) (comp f (inr E D))) := by
  rw [MixCalculation.mix_union,union_pre]
  simp only [← Laws.assoc,← Laws.fst_nat,← Laws.snd_nat]

/-- Both recursive splices use the same original left premise. -/
theorem shared_splice {C Y F H D E X R : NormalForm P}
    (p : Hom Y F) (q : Hom Y H) (f : Hom (.conj C F) D)
    (g : Hom (.conj C H) E) (h : Hom X (.disj C R)) :
    splice h (sharedParent p q f g) =
      comp (sharedInput p q)
        (comp (tensor .conj (splice h g) (splice h f))
          (comp (mix (.disj E R) (.disj D R)) (sharedOutput E D R))) := by
  unfold sharedParent
  rw [mix_paths,union_pre]
  simp only [← Laws.assoc,ProductCalculation.pair_fst,ProductCalculation.pair_snd]
  rw [MixCalculation.splice_union_right]
  simp only [Laws.assoc]
  have hs {V W K : NormalForm P} (a : Hom Y V) (b : Hom (.conj C V) W)
      (k : Hom W K) :
      splice h (comp (tensor .conj (id C) a) (comp b k)) =
        comp (tensor .conj a (id X)) (comp (splice h b) (tensor .disj k (id R))) := by
    rw [← Laws.assoc,Splice.output,Splice.context,Laws.assoc]
  rw [hs,hs]
  rw [← Laws.assoc (tensor .conj (splice h g) (splice h f)),mix_paths]
  simp only [union_pre,union_post,Laws.assoc]
  unfold sharedInput sharedOutput
  simp only [← Laws.assoc,ProductCalculation.pair_fst,ProductCalculation.pair_snd]
  simp only [Laws.assoc]
  have hl : comp (inl (.disj E R) (.disj D R))
      (copair (tensor .disj (inl E D) (id R)) (tensor .disj (inr E D) (id R))) =
      tensor .disj (inl E D) (id R) :=
    (disjDiagonal P).pair_fst (tensor .disj (inl E D) (id R)) (tensor .disj (inr E D) (id R))
  have hr : comp (inr (.disj E R) (.disj D R))
      (copair (tensor .disj (inl E D) (id R)) (tensor .disj (inr E D) (id R))) =
      tensor .disj (inr E D) (id R) :=
    (disjDiagonal P).pair_snd (tensor .disj (inl E D) (id R)) (tensor .disj (inr E D) (id R))
  rw [hl,hr]

end DosenPetric.Reduced.Gentzen.BlockedMix
