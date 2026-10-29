module

public import DosenPetric.ManuscriptSubstitutionSpecializations
public import DosenPetric.CongruenceQuotient

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric
universe u v
namespace Formula
variable {P : Type u} {R : Type v}

abbrev InsertedOccurrences (σ : P → Formula R) := (p : P) × (σ p).Occ

def blockLabel (σ : P → Formula R) (A : Formula P) (x : A.Block σ) : InsertedOccurrences σ :=
  ⟨A.label x.1,x.2⟩

/-- The exact upper map and projections of the displayed block square in §3. -/
theorem block_square (σ : P → Formula R) (A : Formula P) (x : A.Block σ) :
    (blockLabel σ A x).1 = A.label x.1 := rfl

end Formula
namespace Presentation
variable {P : Type u}

/-- The specific p⇒p obstruction stated in §3, using identity versus zero. -/
theorem no_self_exponential (p : P) :
    ¬ Nonempty (ExponentialData (operations P) (.var p) (.var p)) := by
  intro ⟨E⟩
  exact identity_ne_zero p (E.hom_unique (fun _ f g => fromTop_unique f g)
    (Presentation.id (.var p)) (zeroConstruction (.var p)))

/-- The displayed three-arrow alternative to the contextual zero. -/
theorem contextual_zero_alternative (A : Formula P) :
    comp (comp (snd A .bot) (toTop .bot)) (inr A .top) =
      (zeroIdentity P).zeroOf (comp (fst A .bot) (inl A .top)) :=
  (interpretation P).through_top (comp (snd A .bot) (toTop .bot)) (inr A .top)
    (comp (fst A .bot) (inl A .top))

end Presentation
end DosenPetric
