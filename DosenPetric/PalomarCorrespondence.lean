module

public import DosenPetric.PalomarDefinitions
public import DosenPetric.PresentationFragmentMaximality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Palomar.PrimitiveCongruence
universe u
open Presentation
variable {P : Type u} (R : PrimitiveCongruence P)

theorem of_derives {A B : Formula P} {f g : Term P A B} (h : Derives f g) : R.Rel f g := by
  induction h with
  | refl f => exact R.refl f
  | symm _ ih => exact R.symm ih
  | trans _ _ ih ih' => exact R.trans ih ih'
  | comp _ _ ih ih' => exact R.comp ih ih'
  | tensor o _ _ ih ih' => exact R.tensor o ih ih'
  | equation h => exact R.equation h

def quotientRel {A B : Formula P} (f g : Hom A B) : Prop :=
  Quotient.liftOn₂ f g (fun f g => R.Rel f g) (fun f g f' g' hf hg => by
    apply propext
    have hff := R.of_derives hf
    have hgg := R.of_derives hg
    exact ⟨fun h => R.trans (R.symm hff) (R.trans h hgg),
      fun h => R.trans hff (R.trans h (R.symm hgg))⟩)

theorem quotientRel_ofTerm {A B : Formula P} (f g : Term P A B) :
    R.quotientRel (ofTerm f) (ofTerm g) ↔ R.Rel f g := Iff.rfl

/-- Descent to the actual equation-generated quotient, with its genuine
bicartesian fragment operations. -/
def fragment : Congruence (operations P) where
  Rel := R.quotientRel
  refl f := by induction f using Quotient.inductionOn with | h f => exact R.refl f
  symm {A B f g} := by
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g => exact R.symm
  trans {A B f g h} := by
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g =>
    induction h using Quotient.inductionOn with | h h => exact R.trans
  comp {A B C f f' g g'} := by
    induction f using Quotient.inductionOn with | h f =>
    induction f' using Quotient.inductionOn with | h f' =>
    induction g using Quotient.inductionOn with | h g =>
    induction g' using Quotient.inductionOn with | h g' => exact R.comp
  pair {X A B f f' g g'} := by
    induction f using Quotient.inductionOn with | h f =>
    induction f' using Quotient.inductionOn with | h f' =>
    induction g using Quotient.inductionOn with | h g =>
    induction g' using Quotient.inductionOn with | h g' =>
      intro hf hg
      exact R.comp (R.refl _) (R.tensor .conj hf hg)
  copair {A B X f f' g g'} := by
    induction f using Quotient.inductionOn with | h f =>
    induction f' using Quotient.inductionOn with | h f' =>
    induction g using Quotient.inductionOn with | h g =>
    induction g' using Quotient.inductionOn with | h g' =>
      intro hf hg
      exact R.comp (R.tensor .disj hf hg) (R.refl _)

theorem fragment_closed (h : R.Closed) : (substitution P).Closed R.fragment := by
  intro σ A B f g
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => exact h σ

/-- A uniformly substitution-closed primitive congruence extends to a full
proof congruence, preserving its relation on every pair of arrows. -/
def full (h : R.Closed) : ProofCongruence P :=
  .of_closed_fragment R.fragment (R.fragment_closed h)

theorem full_closed (h : R.Closed) : (R.full h).Closed := R.fragment_closed h

theorem full_raw_rel (h : R.Closed) {A B : Formula P} (f g : Term P A B) :
    (R.full h).Rel (ofTerm f) (ofTerm g) ↔ R.Rel f g := Iff.rfl

theorem negate_admissible (h : R.Closed) {A B : Formula P} {f g : Term P A B}
    (hf : R.Rel f g) : R.Rel f.negate g.negate := (R.full h).toRaw.negate hf

def ofFull (Q : ProofCongruence P) : PrimitiveCongruence P where
  Rel f g := Q.Rel (ofTerm f) (ofTerm g)
  refl f := Q.refl (ofTerm f)
  symm := Q.symm
  trans := Q.trans
  equation h := (Presentation.equation h) ▸ Q.refl _
  comp := Q.comp
  tensor o := Q.tensor o

theorem ofFull_closed (Q : ProofCongruence P) (h : Q.Closed) : (ofFull Q).Closed := by
  intro σ A B f g hf
  exact h σ hf

theorem ofFull_full_rel (h : R.Closed) {A B : Formula P} (f g : Term P A B) :
    (ofFull (R.full h)).Rel f g ↔ R.Rel f g := Iff.rfl

theorem full_ofFull_rel (Q : ProofCongruence P) (h : Q.Closed) {A B : Formula P} (f g : Hom A B) :
    ((ofFull Q).full (ofFull_closed Q h)).Rel f g ↔ Q.Rel f g := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => exact Iff.rfl

theorem full_total_iff (h : R.Closed) : (R.full h).Total ↔ R.Total := by
  constructor
  · intro ht A B f g
    exact ht (ofTerm f) (ofTerm g)
  · intro ht A B f g
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g => exact ht f g

theorem ofFull_total_iff (Q : ProofCongruence P) : (ofFull Q).Total ↔ Q.Total := by
  constructor
  · intro ht A B f g
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g => exact ht f g
  · intro ht A B f g
    exact ht (ofTerm f) (ofTerm g)

theorem raw_distinct_iff {A B : Formula P} (f g : Term P A B) :
    (¬ Derives f g) ↔ ofTerm f ≠ ofTerm g :=
  ⟨fun h e => h (Quotient.exact e),fun h e => h (Presentation.sound e)⟩

end DosenPetric.Palomar.PrimitiveCongruence
