module

public import DosenPetric.PositiveFragment

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}

/-- The existing zero-identity law, with no arrows added to empty hom-sets. -/
def zeroIdentity (P : Type u) : ZeroIdentity (category P) where
  zero := zero
  law := Laws.zero_law

/-- A zero between these endpoints requires an existing arrow. -/
def zeroOf {A B : NormalForm P} (f : Hom A B) : Hom A B := comp (zero A) f

theorem zeroOf_independent {A B : NormalForm P} (f g : Hom A B) :
    zeroOf f = zeroOf g := (zeroIdentity P).zeroOf_independent f g

theorem zero_commute {A B : NormalForm P} (f : Hom A B) :
    comp (zero A) f = comp f (zero B) := Laws.zero_law f f

theorem zero_idempotent (A : NormalForm P) : comp (zero A) (zero A) = zero A :=
  (zeroIdentity P).zero_idempotent A

theorem zeroOf_post {A B C : NormalForm P} (f : Hom A B) (g : Hom B C) :
    comp (zeroOf f) g = zeroOf (comp f g) := Laws.assoc _ _ _

theorem zeroOf_pre {A B C : NormalForm P} (f : Hom A B) (g : Hom B C) :
    comp f (zeroOf g) = zeroOf (comp f g) := (zeroIdentity P).precompose f g

theorem conj_ext {X A B : NormalForm P} (f g : Hom X (.conj A B))
    (h₁ : comp f (fst A B) = comp g (fst A B))
    (h₂ : comp f (snd A B) = comp g (snd A B)) : f = g := by
  have hf := (conjDiagonal P).pair_eta f
  have hg := (conjDiagonal P).pair_eta g
  change pair (comp f (fst A B)) (comp f (snd A B)) = f at hf
  change pair (comp g (fst A B)) (comp g (snd A B)) = g at hg
  rw [h₁, h₂] at hf
  exact hf.symm.trans hg

theorem disj_ext {X A B : NormalForm P} (f g : Hom (.disj A B) X)
    (h₁ : comp (inl A B) f = comp (inl A B) g)
    (h₂ : comp (inr A B) f = comp (inr A B) g) : f = g := by
  have hf := (disjDiagonal P).pair_eta f
  have hg := (disjDiagonal P).pair_eta g
  change copair (comp (inl A B) f) (comp (inr A B) f) = f at hf
  change copair (comp (inl A B) g) (comp (inr A B) g) = g at hg
  rw [h₁, h₂] at hf
  exact hf.symm.trans hg

/-- (0I xi), p.288: both tensor factors are zero endomorphisms. -/
theorem tensor_zero (o : Op) (A B : NormalForm P) :
    tensor o (zero A) (zero B) = zero (o.formula A B) := by
  cases o with
  | conj =>
    apply conj_ext
    · rw [← Laws.fst_nat, ← zero_commute]
    · rw [← Laws.snd_nat, ← zero_commute]
  | disj =>
    apply disj_ext
    · rw [Laws.inl_nat, zero_commute]
    · rw [Laws.inr_nat, zero_commute]

theorem tensor_zeroOf (o : Op) {A B C D : NormalForm P}
    (f : Hom A C) (g : Hom B D) :
    tensor o (zeroOf f) (zeroOf g) = zeroOf (tensor o f g) := by
  unfold zeroOf
  rw [← Laws.tensor_comp, tensor_zero]

theorem zeroOf_id (A : NormalForm P) : zeroOf (id A) = zero A := Laws.comp_id _

theorem zeroOf_zero (A : NormalForm P) : zeroOf (zero A) = zero A := zero_idempotent A

namespace Term

def zeroOf {A B : NormalForm P} (f : Term P A B) : Term P A B := .comp (.zero A) f

theorem Positive.zeroOf {A B : NormalForm P} {f : Term P A B} (h : f.Positive) :
    f.zeroOf.Positive := .comp (.zero _) h

theorem Positive.tensor_zero (o : Op) (A B : NormalForm P) :
    (Term.tensor o (.zero A) (.zero B)).Positive := .tensor o (.zero A) (.zero B)

end Term

theorem ofTerm_zeroOf {A B : NormalForm P} (f : Term P A B) :
    ofTerm f.zeroOf = zeroOf (ofTerm f) := rfl

end DosenPetric.Reduced
