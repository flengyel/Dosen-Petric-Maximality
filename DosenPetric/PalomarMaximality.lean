module

public import DosenPetric.PalomarCorrespondence
public import DosenPetric.PresentationShortMaximality
public import DosenPetric.PresentationConsequences

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Palomar
universe u
open Presentation
variable {P : Type u}

/-- If P is nonempty, a congruence closed under uniform substitution is total
whenever it relates two arrow terms not related by `Derives`. -/
theorem maximality [Nonempty P] (R : PrimitiveCongruence P) (closed : R.Closed)
    {A B : Formula P} (f g : Term P A B) (hne : ¬ Derives f g) (hfg : R.Rel f g) : R.Total := by
  have hneq := (PrimitiveCongruence.raw_distinct_iff f g).mp hne
  have ht : R.fragment.Total := Presentation.fragment_maximality R.fragment (R.fragment_closed closed)
    (ofTerm f) (ofTerm g) hneq hfg
  intro C D k l
  exact ht (ofTerm k) (ofTerm l)

/-- The q_A/e_A argument proves maximality using occurrence isolation and
contextual collapse. -/
theorem short_maximality [Nonempty P] (R : PrimitiveCongruence P) (closed : R.Closed)
    {A B : Formula P} (f g : Term P A B) (hne : ¬ Derives f g) (hfg : R.Rel f g) : R.Total := by
  have hneq := (PrimitiveCongruence.raw_distinct_iff f g).mp hne
  obtain ⟨l,hl⟩ := Isolation.normalized_literal_context (interpretation P) (normalization P)
    (interpretation_signedLabel P) R.fragment (ofTerm f) (ofTerm g) hneq hfg
  have allK : ∀ C, ContextualCollapse.K R.fragment (Z:=zeroIdentity P) C :=
    ContextualCollapse.all_contexts R.fragment (substitution P) (doubleNegation P)
      (R.fragment_closed closed) l hl
  intro C D k l
  exact ShortProof.total R.fragment allK (ofTerm k) (ofTerm l)

/-- If P is nonempty, every congruence closed under uniform substitution
either coincides with `Derives` or relates all parallel arrow terms. -/
theorem congruence_dichotomy [Nonempty P] (R : PrimitiveCongruence P) (closed : R.Closed) :
    (∀ {A B} (f g : Term P A B), R.Rel f g ↔ Derives f g) ∨ R.Total := by
  classical
  by_cases h : ∀ {A B} (f g : Term P A B), R.Rel f g → Derives f g
  · left
    intro A B f g
    exact ⟨h f g,R.of_derives⟩
  · right
    have hex : ∃ A B, ∃ f g : Term P A B, R.Rel f g ∧ ¬ Derives f g := by
      apply Classical.byContradiction
      intro hn
      apply h
      intro A B f g hf
      apply Classical.byContradiction
      intro hne
      exact hn ⟨A,B,f,g,hf,hne⟩
    obtain ⟨A,B,f,g,hfg,hne⟩ := hex
    intro C D k l
    exact maximality R closed f g hne hfg k l

/-- The identity and zero endomorphism of every variable are distinct. -/
theorem identity_ne_zero (p : P) : ¬ Derives (Term.id (.var p)) (Term.zero (.var p)) := by
  intro h
  exact Presentation.identity_ne_primitive_zero p (Presentation.sound h)

/-- There is no arrow term from the terminal object to the initial object. -/
theorem no_top_to_bot (P : Type u) : ¬ Nonempty (Term P .top .bot) := by
  intro ⟨f⟩
  exact Presentation.empty_hom P ⟨ofTerm f⟩

end DosenPetric.Palomar
