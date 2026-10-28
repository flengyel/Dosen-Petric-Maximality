module

public import DosenPetric.GentzenCutDistribution

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ProductCalculation

theorem ext {X A B : NormalForm P} (f g : Hom X (.conj A B))
    (h₁ : comp f (fst A B) = comp g (fst A B))
    (h₂ : comp f (snd A B) = comp g (snd A B)) : f = g :=
  (conjDiagonal P).ext f g h₁ h₂

theorem pair_fst {X A B : NormalForm P} (f : Hom X A) (g : Hom X B) :
    comp (pair f g) (fst A B) = f := (conjDiagonal P).pair_fst f g

theorem pair_snd {X A B : NormalForm P} (f : Hom X A) (g : Hom X B) :
    comp (pair f g) (snd A B) = g := (conjDiagonal P).pair_snd f g

theorem pair_pre {W X A B : NormalForm P} (h : Hom W X) (f : Hom X A) (g : Hom X B) :
    comp h (pair f g) = pair (comp h f) (comp h g) := (conjDiagonal P).pair_pre h f g

theorem pair_fst_comp {X A B C : NormalForm P} (f : Hom X A) (g : Hom X B) (h : Hom A C) :
    comp (pair f g) (comp (fst A B) h) = comp f h := by
  rw [← Laws.assoc, pair_fst]

theorem pair_snd_comp {X A B C : NormalForm P} (f : Hom X A) (g : Hom X B) (h : Hom B C) :
    comp (pair f g) (comp (snd A B) h) = comp g h := by
  rw [← Laws.assoc, pair_snd]

theorem tensor_pair {A B C D : NormalForm P} (f : Hom A C) (g : Hom B D) :
    tensor .conj f g = pair (comp (fst A B) f) (comp (snd A B) g) := by
  apply ext
  · rw [pair_fst, ← Laws.fst_nat]
  · rw [pair_snd, ← Laws.snd_nat]

theorem swap_pair (A B : NormalForm P) :
    swap .conj A B = pair (snd A B) (fst A B) := by
  apply ext
  · rw [pair_fst, ← Laws.snd_swap]
  · rw [pair_snd, swap_snd]

theorem assocR_pair (A B C : NormalForm P) :
    assocR .conj A B C =
      pair (pair (fst A (.conj B C)) (comp (snd A (.conj B C)) (fst B C)))
        (comp (snd A (.conj B C)) (snd B C)) :=
  (conjDiagonal P).assocR_pair (rightOut_assocR .conj) A B C

theorem assocL_pair (A B C : NormalForm P) :
    assocL .conj A B C =
      pair (comp (fst (.conj A B) C) (fst A B))
        (pair (comp (fst (.conj A B) C) (snd A B)) (snd (.conj A B) C)) :=
  (conjDiagonal P).assocL_pair (rightOut_assocR .conj) A B C

/-- The structural output adapter in the principal conjunction reduction. -/
theorem principal_finish (T B A : NormalForm P) :
    comp (CutDistribution.finish T B A)
        (comp (swap .conj T (.conj A B)) (assocL .conj A B T)) =
      comp (tensor .conj (swap .conj T B) (id A)) (swap .conj (.conj B T) A) := by
  unfold CutDistribution.finish
  simp only [assocL_pair, swap_pair, tensor_pair, pair_pre,
    pair_fst, pair_snd, pair_fst_comp, pair_snd_comp, Laws.comp_id]

/-- Reordering fixed contexts before the second principal component cut. -/
theorem principal_input (T X B : NormalForm P) :
    comp (assocL .conj T X B)
        (comp (tensor .conj (id T) (swap .conj X B))
          (comp (assocR .conj T B X) (tensor .conj (swap .conj T B) (id X)))) =
      comp (swap .conj (.conj T X) B) (assocR .conj B T X) := by
  simp only [assocL_pair, assocR_pair, swap_pair, tensor_pair, pair_pre,
    pair_fst, pair_snd, pair_fst_comp, pair_snd_comp, Laws.comp_id]

def rotate (T X B : NormalForm P) : Hom (.conj (.conj T X) B) (.conj (.conj B T) X) :=
  comp (swap .conj (.conj T X) B) (assocR .conj B T X)

theorem rotate_naturality {T X X' B : NormalForm P} (f : Hom X X') :
    comp (rotate T X B) (tensor .conj (id (.conj B T)) f) =
      comp (tensor .conj (tensor .conj (id T) f) (id B)) (rotate T X' B) := by
  unfold rotate
  simp only [assocR_pair, swap_pair, tensor_pair, pair_pre, pair_fst, pair_snd,
    pair_fst_comp, pair_snd_comp, Laws.comp_id]
  rw [Laws.assoc]

end ProductCalculation
end DosenPetric.Reduced.Gentzen
