module

public import DosenPetric.PresentationNegationTerms

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation
universe u

/-- Congruences for every arrow operation in the source presentation.
The primitive operations with arrow arguments are composition and the two
covariant tensors. Negation is the explicit derived operation above. -/
structure ProofCongruence (P : Type u) where
  Rel : {A B : Formula P} → Hom A B → Hom A B → Prop
  refl : ∀ {A B} (f : Hom A B), Rel f f
  symm : ∀ {A B} {f g : Hom A B}, Rel f g → Rel g f
  trans : ∀ {A B} {f g h : Hom A B}, Rel f g → Rel g h → Rel f h
  comp : ∀ {A B C} {f f' : Hom A B} {g g' : Hom B C},
    Rel f f' → Rel g g' → Rel (Presentation.comp f g) (Presentation.comp f' g')
  tensor : ∀ o {A B C D} {f f' : Hom A C} {g g' : Hom B D},
    Rel f f' → Rel g g' → Rel (Presentation.tensor o f g) (Presentation.tensor o f' g')
  negate : ∀ {A B} {f g : Hom A B}, Rel f g → Rel (Presentation.negate f) (Presentation.negate g)

namespace ProofCongruence
variable {P : Type u} (Q : ProofCongruence P)

def Closed : Prop := ∀ σ {A B} {f g : Hom A B}, Q.Rel f g → Q.Rel (substitute σ f) (substitute σ g)

theorem pair {X A B : Formula P} {f f' : Hom X A} {g g' : Hom X B}
    (hf : Q.Rel f f') (hg : Q.Rel g g') : Q.Rel (Presentation.pair f g) (Presentation.pair f' g') :=
  Q.comp (Q.refl _) (Q.tensor .conj hf hg)

theorem copair {A B X : Formula P} {f f' : Hom A X} {g g' : Hom B X}
    (hf : Q.Rel f f') (hg : Q.Rel g g') : Q.Rel (Presentation.copair f g) (Presentation.copair f' g') :=
  Q.comp (Q.tensor .disj hf hg) (Q.refl _)

def fragment : Congruence (operations P) where
  Rel := Q.Rel
  refl := Q.refl
  symm := Q.symm
  trans := Q.trans
  comp := Q.comp
  pair := Q.pair
  copair := Q.copair

theorem fragment_closed (h : Q.Closed) : (substitution P).Closed Q.fragment := h

def Total : Prop := ∀ {A B} (f g : Hom A B), Q.Rel f g

end ProofCongruence

/-- The corresponding equivalence relation on typed raw source terms. -/
structure RawProofCongruence (P : Type u) where
  Rel : {A B : Formula P} → Term P A B → Term P A B → Prop
  refl : ∀ {A B} (f : Term P A B), Rel f f
  symm : ∀ {A B} {f g : Term P A B}, Rel f g → Rel g f
  trans : ∀ {A B} {f g h : Term P A B}, Rel f g → Rel g h → Rel f h
  equation : ∀ {A B} {f g : Term P A B}, Equation f g → Rel f g
  comp : ∀ {A B C} {f f' : Term P A B} {g g' : Term P B C},
    Rel f f' → Rel g g' → Rel (.comp f g) (.comp f' g')
  tensor : ∀ o {A B C D} {f f' : Term P A C} {g g' : Term P B D},
    Rel f f' → Rel g g' → Rel (.tensor o f g) (.tensor o f' g')
  negate : ∀ {A B} {f g : Term P A B}, Rel f g → Rel f.negate g.negate

namespace RawProofCongruence
variable {P : Type u} (Q : RawProofCongruence P)

def Closed : Prop := ∀ σ {A B} {f g : Term P A B}, Q.Rel f g → Q.Rel (f.subst σ) (g.subst σ)

theorem of_derives {A B : Formula P} {f g : Term P A B} (h : Derives f g) : Q.Rel f g := by
  induction h with
  | refl f => exact Q.refl f
  | symm _ ih => exact Q.symm ih
  | trans _ _ ih ih' => exact Q.trans ih ih'
  | equation h => exact Q.equation h
  | comp _ _ ih ih' => exact Q.comp ih ih'
  | tensor o _ _ ih ih' => exact Q.tensor o ih ih'

def quotientRel {A B : Formula P} (f g : Hom A B) : Prop :=
  Quotient.liftOn₂ f g (fun f g => Q.Rel f g) (fun f g f' g' hf hg => by
    apply propext
    have hff := Q.of_derives hf
    have hgg := Q.of_derives hg
    exact ⟨fun h => Q.trans (Q.symm hff) (Q.trans h hgg),
      fun h => Q.trans hff (Q.trans h (Q.symm hgg))⟩)

theorem quotientRel_ofTerm {A B : Formula P} (f g : Term P A B) :
    Q.quotientRel (ofTerm f) (ofTerm g) ↔ Q.Rel f g := Iff.rfl

def toQuotient : ProofCongruence P where
  Rel := Q.quotientRel
  refl f := by induction f using Quotient.inductionOn with | h f => exact Q.refl f
  symm {A B f g} := by
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g => exact Q.symm
  trans {A B f g h} := by
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g =>
    induction h using Quotient.inductionOn with | h h => exact Q.trans
  comp {A B C f f' g g'} := by
    induction f using Quotient.inductionOn with | h f =>
    induction f' using Quotient.inductionOn with | h f' =>
    induction g using Quotient.inductionOn with | h g =>
    induction g' using Quotient.inductionOn with | h g' => exact Q.comp
  tensor o {A B C D f f' g g'} := by
    induction f using Quotient.inductionOn with | h f =>
    induction f' using Quotient.inductionOn with | h f' =>
    induction g using Quotient.inductionOn with | h g =>
    induction g' using Quotient.inductionOn with | h g' => exact Q.tensor o
  negate {A B f g} := by
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g =>
    change Q.Rel f g → Q.quotientRel (Presentation.negate (ofTerm f)) (Presentation.negate (ofTerm g))
    rw [← negateTerm_denotes,← negateTerm_denotes]
    exact Q.negate

theorem toQuotient_closed (h : Q.Closed) : Q.toQuotient.Closed := by
  intro σ A B f g
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => exact h σ

end RawProofCongruence
namespace ProofCongruence
variable {P : Type u} (Q : ProofCongruence P)

def toRaw : RawProofCongruence P where
  Rel f g := Q.Rel (ofTerm f) (ofTerm g)
  refl f := Q.refl _
  symm := Q.symm
  trans := Q.trans
  equation h := (Presentation.equation h) ▸ Q.refl _
  comp := Q.comp
  tensor o {A B C D f f' g g'} hf hg := Q.tensor o hf hg
  negate h := by rw [negateTerm_denotes,negateTerm_denotes]; exact Q.negate h

theorem toRaw_closed (h : Q.Closed) : Q.toRaw.Closed := by
  intro σ A B f g hf
  exact h σ hf

theorem raw_quotient_rel {A B : Formula P} (f g : Hom A B) :
    Q.toRaw.toQuotient.Rel f g ↔ Q.Rel f g := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => exact Iff.rfl

end ProofCongruence
namespace RawProofCongruence
variable {P : Type u} (Q : RawProofCongruence P)

theorem quotient_raw_rel {A B : Formula P} (f g : Term P A B) :
    Q.toQuotient.toRaw.Rel f g ↔ Q.Rel f g := Iff.rfl

end RawProofCongruence
end DosenPetric.Presentation
