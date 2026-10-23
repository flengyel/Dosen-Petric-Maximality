module

public import DosenPetric.ReducedZeroAlgebra

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}

namespace Term
/-- The derived path `A → A ∧ A → B ∧ B → B ∨ B → B`. -/
def union {A B : NormalForm P} (f g : Term P A B) : Term P A B :=
  .comp (.diag A) (.comp (.tensor .conj f g) (.comp (.mix B B) (.codiag B)))

theorem Positive.union {A B : NormalForm P} {f g : Term P A B}
    (hf : f.Positive) (hg : g.Positive) : (f.union g).Positive :=
  .comp (.diag _) (.comp (.tensor _ hf hg) (.comp (.mix ..) (.codiag _)))
end Term

theorem Derives.union {A B : NormalForm P} {f f' g g' : Term P A B}
    (hf : Derives f f') (hg : Derives g g') : Derives (f.union g) (f'.union g') :=
  .comp (.refl _) (.comp (.tensor _ hf hg) (.refl _))

def union {A B : NormalForm P} (f g : Hom A B) : Hom A B :=
  Quotient.liftOn₂ f g (fun f g => ofTerm (f.union g))
    (fun _ _ _ _ hf hg => sound (hf.union hg))

theorem union_ofTerm {A B : NormalForm P} (f g : Term P A B) :
    union (ofTerm f) (ofTerm g) = ofTerm (f.union g) := rfl

/-- The natural commutative, associative merge derived from mix and codiagonal. -/
def merge (A : NormalForm P) : Hom (.conj A A) A := comp (mix A A) (codiag A)

theorem union_def {A B : NormalForm P} (f g : Hom A B) :
    union f g = comp (diag A) (comp (tensor .conj f g) (merge B)) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

/-- The source convention on p.220 uses (f or g) after mix at A. -/
theorem union_source {A B : NormalForm P} (f g : Hom A B) :
    union f g = comp (diag A) (comp (mix A A) (comp (tensor .disj f g) (codiag B))) := by
  rw [union_def, merge, ← Laws.assoc (tensor .conj f g), ← Laws.mix_nat, Laws.assoc]

theorem merge_nat {A B : NormalForm P} (f : Hom A B) :
    comp (merge A) f = comp (tensor .conj f f) (merge B) := by
  unfold merge
  rw [Laws.assoc, ← Laws.codiag_nat, ← Laws.assoc, Laws.mix_nat, Laws.assoc]

theorem merge_swap (A : NormalForm P) : comp (swap .conj A A) (merge A) = merge A := by
  unfold merge
  rw [← Laws.assoc, Laws.mix_swap, Laws.assoc, Laws.codiag_swap]

theorem codiag_assoc_forward (A : NormalForm P) :
    comp (assocR .disj A A A) (comp (tensor .disj (codiag A) (id A)) (codiag A)) =
      comp (tensor .disj (id A) (codiag A)) (codiag A) := by
  rw [← Laws.codiag_assoc, ← Laws.assoc, Laws.assocR_L, Laws.id_comp]

theorem merge_assoc (A : NormalForm P) :
    comp (assocR .conj A A A) (comp (tensor .conj (merge A) (id A)) (merge A)) =
      comp (tensor .conj (id A) (merge A)) (merge A) := by
  unfold merge
  have hs : tensor .conj (comp (mix A A) (codiag A)) (id A) =
      comp (tensor .conj (mix A A) (id A)) (tensor .conj (codiag A) (id A)) := by
    rw [Laws.tensor_comp, Laws.id_comp]
  rw [hs]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (codiag A) (id A)), ← Laws.mix_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (mix A A) (id A)), ← Laws.mix_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocR .conj A A A) (mix (.conj A A) A),
    ← Laws.assoc (comp (assocR .conj A A A) (mix (.conj A A) A)),
    Laws.assoc (assocR .conj A A A) (mix (.conj A A) A), Laws.mix_assoc]
  simp only [Laws.assoc]
  rw [codiag_assoc_forward, ← Laws.assoc (mix A (.disj A A)), Laws.mix_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id A) (mix A A)), Laws.tensor_comp, Laws.id_comp]

theorem union_pre {X A B : NormalForm P} (h : Hom X A) (f g : Hom A B) :
    comp h (union f g) = union (comp h f) (comp h g) := by
  simp only [union_def]
  rw [← Laws.assoc h, ← Laws.diag_nat, Laws.assoc, ← Laws.assoc (tensor .conj h h), Laws.tensor_comp]

theorem union_post {A B C : NormalForm P} (f g : Hom A B) (h : Hom B C) :
    comp (union f g) h = union (comp f h) (comp g h) := by
  simp only [union_def, Laws.assoc]
  rw [merge_nat, ← Laws.assoc (tensor .conj f g), Laws.tensor_comp]

theorem union_comm {A B : NormalForm P} (f g : Hom A B) : union f g = union g f := by
  simp only [union_def]
  calc
    _ = comp (diag A) (comp (swap .conj A A) (comp (tensor .conj f g) (merge B))) := by
      rw [← Laws.assoc (diag A) (swap .conj A A), Laws.diag_swap]
    _ = _ := by rw [← Laws.assoc (swap .conj A A), Laws.swap_nat, Laws.assoc, merge_swap]

theorem union_idem {A B : NormalForm P} (f : Hom A B) : union f f = f := by
  rw [union_def, ← Laws.assoc, Laws.diag_nat, Laws.assoc]
  change comp f (comp (diag B) (comp (mix B B) (codiag B))) = f
  rw [Laws.diag_mix_codiag, Laws.comp_id]

theorem pair_pre {X A B C : NormalForm P} (h : Hom X A) (f : Hom A B) (g : Hom A C) :
    comp h (pair f g) = pair (comp h f) (comp h g) := by
  change comp h (comp (diag A) (tensor .conj f g)) =
    comp (diag X) (tensor .conj (comp h f) (comp h g))
  rw [← Laws.assoc, ← Laws.diag_nat, Laws.assoc, Laws.tensor_comp]

theorem pair_post {X A B C D : NormalForm P} (f : Hom X A) (g : Hom X B)
    (h : Hom A C) (k : Hom B D) :
    comp (pair f g) (tensor .conj h k) = pair (comp f h) (comp g k) := by
  change comp (comp (diag X) (tensor .conj f g)) (tensor .conj h k) = _
  rw [Laws.assoc, Laws.tensor_comp]
  rfl

theorem pair_assoc {X A B C : NormalForm P} (f : Hom X A) (g : Hom X B) (h : Hom X C) :
    comp (pair f (pair g h)) (assocR .conj A B C) = pair (pair f g) h := by
  change comp (comp (diag X) (tensor .conj f (comp (diag X) (tensor .conj g h))))
    (assocR .conj A B C) =
      comp (diag X) (tensor .conj (comp (diag X) (tensor .conj f g)) h)
  have hs : tensor .conj f (comp (diag X) (tensor .conj g h)) =
      comp (tensor .conj (id X) (diag X)) (tensor .conj f (tensor .conj g h)) := by
    rw [Laws.tensor_comp, Laws.id_comp]
  rw [hs]
  simp only [Laws.assoc]
  rw [← Laws.assocR_nat]
  simp only [← Laws.assoc]
  rw [Laws.assoc (diag X), Laws.diag_assoc]
  simp only [Laws.assoc]
  rw [Laws.tensor_comp, Laws.id_comp]

theorem union_assoc {A B : NormalForm P} (f g h : Hom A B) :
    union (union f g) h = union f (union g h) := by
  have hu (s t : Hom A B) : union s t = comp (pair s t) (merge B) := by
    rw [union_def, ← Laws.assoc]; rfl
  simp only [hu]
  have hl : pair (comp (pair f g) (merge B)) h =
      comp (pair (pair f g) h) (tensor .conj (merge B) (id B)) := by
    rw [pair_post, Laws.comp_id]
  have hr : pair f (comp (pair g h) (merge B)) =
      comp (pair f (pair g h)) (tensor .conj (id B) (merge B)) := by
    rw [pair_post, Laws.comp_id]
  rw [hl, hr, ← pair_assoc, Laws.assoc, Laws.assoc, merge_assoc, Laws.assoc]

/-- Direct derivation on p.291, using (d m), (0I), (d k), naturality and (w k). -/
theorem union_id_zero (A : NormalForm P) : union (id A) (zero A) = id A := by
  rw [union_def]
  unfold merge
  rw [Laws.dist_mix A A A]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id A) (zero A)), Laws.tensor_comp, Laws.id_comp]
  have hz : comp (zero A) (inr A A) = comp (zero A) (inl A A) :=
    zeroOf_independent (inr A A) (inl A A)
  have ht : tensor .conj (id A) (comp (zero A) (inl A A)) =
      comp (tensor .conj (id A) (zero A)) (tensor .conj (id A) (inl A A)) := by
    rw [Laws.tensor_comp, Laws.id_comp]
  rw [hz, ht, Laws.assoc, ← Laws.assoc (tensor .conj (id A) (inl A A)), ← Laws.dist_inl]
  rw [← Laws.assoc (inl (.conj A A) A), Laws.inl_nat]
  have hf : comp (comp (diag A) (tensor .conj (id A) (zero A))) (fst A A) = id A := by
    rw [Laws.assoc, ← Laws.fst_nat, ← Laws.assoc, Laws.diag_fst, Laws.id_comp]
  simp only [← Laws.assoc]
  rw [hf, Laws.id_comp, Laws.inl_codiag]

theorem union_zeroOf {A B : NormalForm P} (f w : Hom A B) : union f (zeroOf w) = f := by
  rw [zeroOf_independent w f]
  have h := union_post (id A) (zero A) f
  rw [union_id_zero, Laws.id_comp] at h
  exact h.symm

theorem zeroOf_union {A B : NormalForm P} (f w : Hom A B) : union (zeroOf w) f = f := by
  rw [union_comm, union_zeroOf]

end DosenPetric.Reduced
