module

public import DosenPetric.GentzenBinaryParametricDescent
public import DosenPetric.ReducedUnion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace MixCalculation

/-- Tensoring a fixed arrow with a union distributes over its two summands. -/
theorem conj_union_right {A B X Y : NormalForm P} (h : Hom A B) (f g : Hom X Y) :
    tensor .conj h (union f g) = union (tensor .conj h f) (tensor .conj h g) := by
  apply Reduced.conj_ext
  · rw [← Laws.fst_nat,union_post,← Laws.fst_nat,← Laws.fst_nat,union_idem]
  · rw [← Laws.snd_nat,union_post,← Laws.snd_nat,← Laws.snd_nat,union_pre]

theorem conj_union_left {A B X Y : NormalForm P} (f g : Hom A B) (h : Hom X Y) :
    tensor .conj (union f g) h = union (tensor .conj f h) (tensor .conj g h) := by
  apply Reduced.conj_ext
  · rw [← Laws.fst_nat,union_post,← Laws.fst_nat,← Laws.fst_nat,union_pre]
  · rw [← Laws.snd_nat,union_post,← Laws.snd_nat,← Laws.snd_nat,union_idem]

theorem disj_union_right {A B X Y : NormalForm P} (h : Hom A B) (f g : Hom X Y) :
    tensor .disj h (union f g) = union (tensor .disj h f) (tensor .disj h g) := by
  apply Reduced.disj_ext
  · rw [Laws.inl_nat,union_pre,Laws.inl_nat,Laws.inl_nat,union_idem]
  · rw [Laws.inr_nat,union_pre,Laws.inr_nat,Laws.inr_nat,union_post]

theorem disj_union_left {A B X Y : NormalForm P} (f g : Hom A B) (h : Hom X Y) :
    tensor .disj (union f g) h = union (tensor .disj f h) (tensor .disj g h) := by
  apply Reduced.disj_ext
  · rw [Laws.inl_nat,union_pre,Laws.inl_nat,Laws.inl_nat,union_post]
  · rw [Laws.inr_nat,union_pre,Laws.inr_nat,Laws.inr_nat,union_idem]

/-- Mix is the union of its two projection-injection paths. -/
theorem mix_union (A B : NormalForm P) :
    mix A B = union (comp (fst A B) (inl A B)) (comp (snd A B) (inr A B)) := by
  symm
  rw [union_def,merge]
  have ht : tensor .conj (comp (fst A B) (inl A B)) (comp (snd A B) (inr A B)) =
      comp (tensor .conj (fst A B) (snd A B)) (tensor .conj (inl A B) (inr A B)) := by
    rw [Laws.tensor_comp]
  rw [ht]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (inl A B) (inr A B)),← Laws.mix_nat]
  simp only [← Laws.assoc]
  have hi : comp (diag (.conj A B)) (tensor .conj (fst A B) (snd A B)) = id (.conj A B) := by
    simpa only [DiagonalData.pair,conjDiagonal,conjMonoidal,category,Laws.id_comp] using (conjDiagonal P).pair_eta (id (.conj A B))
  rw [hi,Laws.id_comp]
  have ho : comp (tensor .disj (inl A B) (inr A B)) (codiag (.disj A B)) = id (.disj A B) := by
    simpa only [DiagonalData.pair,disjDiagonal,disjMonoidal,opposite,category,Laws.comp_id] using (disjDiagonal P).pair_eta (id (.disj A B))
  rw [Laws.assoc,ho,Laws.comp_id]

/-- The selected-cut splice distributes over a union in either premise. -/
theorem splice_union_left {X Y C D Z : NormalForm P} (f h : Hom X (.disj C D))
    (g : Hom (.conj C Y) Z) :
    splice (union f h) g = union (splice f g) (splice h g) := by
  simp only [splice,conj_union_right,union_post]

theorem splice_union_right {X Y C D Z : NormalForm P} (f : Hom X (.disj C D))
    (g h : Hom (.conj C Y) Z) :
    splice f (union g h) = union (splice f g) (splice f h) := by
  simp only [splice,union_pre,disj_union_left]

/-- The two native mix children occupy the second and first context blocks,
    respectively, in both the input and output. -/
theorem native_mix_union {Γ Θ Δ Λ : List (NormalForm P)} (f : G P Γ Δ) (g : G P Θ Λ) :
    ofTerm (G.mix f g).denote =
      union
        (comp (ofTerm (append .conj Θ Γ).invTerm)
          (comp (snd (ante Θ) (ante Γ))
            (comp (ofTerm f.denote)
              (comp (inr (succ Λ) (succ Δ)) (ofTerm (append .disj Λ Δ).toTerm)))))
        (comp (ofTerm (append .conj Θ Γ).invTerm)
          (comp (fst (ante Θ) (ante Γ))
            (comp (ofTerm g.denote)
              (comp (inl (succ Λ) (succ Δ)) (ofTerm (append .disj Λ Δ).toTerm))))) := by
  simp only [G.denote,Rules.mix,ofTerm_comp,ofTerm_tensor,mix_term]
  rw [mix_union]
  simp only [union_pre,union_post,Laws.assoc]
  rw [← Laws.assoc (tensor .conj (ofTerm g.denote) (ofTerm f.denote)),← Laws.fst_nat]
  rw [← Laws.assoc (tensor .conj (ofTerm g.denote) (ofTerm f.denote)),← Laws.snd_nat]
  simp only [Laws.assoc]
  exact union_comm _ _

end MixCalculation
end DosenPetric.Reduced.Gentzen
