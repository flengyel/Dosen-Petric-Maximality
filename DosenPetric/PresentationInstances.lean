module

public import DosenPetric.PresentationSubstitution
public import DosenPetric.PresentationZero
public import DosenPetric.Substitution

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.Presentation

universe u

variable {P : Type u}

/-- The product unit arrow is the manuscript's pairing with the terminal arrow. -/
theorem rightIn_conj_eq_pair (A : Formula P) :
    rightIn .conj A = pair (id A) (toTop A) := by
  have h := (operations P).pair_eta (rightIn .conj A)
  change pair (comp (rightIn .conj A) (fst A .top))
    (comp (rightIn .conj A) (snd A .top)) = rightIn .conj A at h
  rw [Laws.fst_top, Laws.rightIn_Out] at h
  exact h.symm

/-- The coproduct unit arrow is the manuscript's copairing with the initial arrow. -/
theorem leftOut_disj_eq_copair (A : Formula P) :
    leftOut .disj A = copair (fromBot A) (id A) := by
  have h := (operations P).copair_eta (leftOut .disj A)
  change copair (comp (inl .bot A) (leftOut .disj A))
    (comp (inr .bot A) (leftOut .disj A)) = leftOut .disj A at h
  have hi := (operations P).fromBot_unique (comp (inl .bot A) (leftOut .disj A))
  change comp (inl .bot A) (leftOut .disj A) = fromBot A at hi
  have hr := (disjDiagonal P).snd_unit A
  change inr .bot A = leftIn .disj A at hr
  rw [hi, hr, Laws.leftIn_Out] at h
  exact h.symm

/-- The source unit-isomorphism formula is exactly the manuscript §2 formula. -/
theorem zeroConstruction_structural (A : Formula P) : zeroConstruction A =
    comp (pair (id A) (toTop A))
      (comp (tensor .conj (id A) (excludedMiddle A))
        (comp (dist A (.neg A) A)
          (comp (tensor .disj (contradiction A) (id A))
            (copair (fromBot A) (id A))))) := by
  rw [zeroConstruction_def, rightIn_conj_eq_pair, leftOut_disj_eq_copair]

/-- Whole-arrow substitution for the source quotient, including the constructed zero. -/
def substitution (P : Type u) : Substitution (operations P) (zeroIdentity P) where
  map := substitute
  map_id := substitute_id
  map_comp := substitute_comp
  map_fst _ _ _ := rfl
  map_snd _ _ _ := rfl
  map_pair σ {X A B} f g := by
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g => rfl
  map_inl _ _ _ := rfl
  map_inr _ _ _ := rfl
  map_copair σ {A B X} f g := by
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g => rfl
  map_toTop _ _ := rfl
  map_fromBot _ _ := rfl
  map_dist _ _ _ _ := rfl
  map_zero _ _ := rfl

/-- The two n-arrows instantiate the double-negation retract without coherence. -/
def doubleNegation (P : Type u) : DoubleNegation (category P) where
  into := dnIn
  out := dnOut
  into_out := Laws.dnOut_out
  out_into := Laws.dnOut_in

end DosenPetric.Presentation
