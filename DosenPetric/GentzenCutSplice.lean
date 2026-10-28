module

public import DosenPetric.GentzenAtomicCutElimination

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- The contextual cut before the two canonical context-fold comparisons. -/
def splice {X Y C D Z : NormalForm P} (f : Hom X (.disj C D))
    (g : Hom (.conj C Y) Z) : Hom (.conj Y X) (.disj Z D) :=
  comp (tensor .conj (id Y) f)
    (comp (dist Y C D) (tensor .disj (comp (swap .conj Y C) g) (id D)))

namespace Splice
variable {X X' Y Y' C D D' Z Z' : NormalForm P}

theorem input (k : Hom X' X) (f : Hom X (.disj C D)) (g : Hom (.conj C Y) Z) :
    splice (comp k f) g = comp (tensor .conj (id Y) k) (splice f g) := by
  simp only [splice, ← Laws.assoc, Laws.tensor_comp, Laws.id_comp]

theorem output (f : Hom X (.disj C D)) (g : Hom (.conj C Y) Z) (k : Hom Z Z') :
    splice f (comp g k) = comp (splice f g) (tensor .disj k (id D)) := by
  simp only [splice, Laws.assoc, Laws.tensor_comp, Laws.id_comp]

theorem context (k : Hom Y' Y) (f : Hom X (.disj C D)) (g : Hom (.conj C Y) Z) :
    splice f (comp (tensor .conj (id C) k) g) =
      comp (tensor .conj k (id X)) (splice f g) := by
  have hd := Laws.dist_nat k (id C) (id D)
  have hs := Laws.swap_nat .conj k (id C)
  have ht : tensor .conj k f = comp (tensor .conj (id Y') f)
      (tensor .conj k (id (.disj C D))) := by
    rw [Laws.tensor_comp, Laws.id_comp, Laws.comp_id]
  symm
  unfold splice
  rw [← Laws.assoc (tensor .conj k (id X)), Laws.tensor_comp, Laws.comp_id, Laws.id_comp, ht]
  simp only [Laws.assoc]
  have he : comp (tensor .conj k (id (.disj C D))) (dist Y C D) =
      comp (dist Y' C D) (tensor .disj (tensor .conj k (id C)) (id D)) := by
    simpa only [Laws.tensor_id] using hd.symm
  rw [← Laws.assoc (tensor .conj k (id (.disj C D))), he]
  simp only [Laws.assoc]
  rw [Laws.tensor_comp, Laws.comp_id]
  rw [← Laws.assoc (tensor .conj k (id C)), ← hs, Laws.assoc]

theorem residual (k : Hom D D') (f : Hom X (.disj C D)) (g : Hom (.conj C Y) Z) :
    splice (comp f (tensor .disj (id C) k)) g =
      comp (splice f g) (tensor .disj (id Z) k) := by
  have hd : comp (tensor .conj (id Y) (tensor .disj (id C) k)) (dist Y C D') =
      comp (dist Y C D) (tensor .disj (id (.conj Y C)) k) := by
    simpa only [Laws.tensor_id] using (Laws.dist_nat (id Y) (id C) k).symm
  unfold splice
  rw [tensor_factor .conj (id Y) f (tensor .disj (id C) k)]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id Y) (tensor .disj (id C) k)), hd]
  simp only [Laws.assoc]
  simp only [Laws.tensor_comp, Laws.id_comp, Laws.comp_id]

end Splice

theorem cut_splice {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) :
    ofTerm (G.cut f g).denote =
      comp (ofTerm (append .conj Θ Γ).invTerm)
        (comp (splice (ofTerm f.denote) (ofTerm g.denote))
          (ofTerm (append .disj Λ Δ).toTerm)) := by
  simp only [G.denote, Rules.cut, ofTerm_comp, ofTerm_tensor, ofTerm_id,
    term_dist, term_swap, splice, Laws.assoc]

end DosenPetric.Reduced.Gentzen
