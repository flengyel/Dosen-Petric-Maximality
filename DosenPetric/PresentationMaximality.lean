module

public import DosenPetric.PresentationProofCongruence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation
universe u
variable {P : Type u}

/-- Maximality for the actual source quotient and its full proof congruences. -/
theorem maximality (Q : ProofCongruence P) (closed : Q.Closed)
    {A B : Formula P} (f g : Hom A B) (hne : f ≠ g) (hfg : Q.Rel f g) : Q.Total :=
  relative_maximality (interpretation P) (normalization P) (interpretation_signedLabel P)
    (substitution P) (doubleNegation P) Q.fragment (Q.fragment_closed closed) f g hne hfg

/-- The only uniformly substitution-closed full proof congruences are equality
and the total relation on the arrows of each existing hom-set. -/
theorem congruence_dichotomy (Q : ProofCongruence P) (closed : Q.Closed) :
    (∀ {A B} (f g : Hom A B), Q.Rel f g ↔ f = g) ∨ Q.Total := by
  classical
  by_cases h : ∀ {A B} (f g : Hom A B), Q.Rel f g → f = g
  · left
    intro A B f g
    exact ⟨h f g,fun e => e ▸ Q.refl f⟩
  · right
    have hex : ∃ A B, ∃ f g : Hom A B, Q.Rel f g ∧ f ≠ g := by
      apply Classical.byContradiction
      intro hn
      apply h
      intro A B f g hf
      apply Classical.byContradiction
      intro hne
      exact hn ⟨A,B,f,g,hf,hne⟩
    obtain ⟨A,B,f,g,hfg,hne⟩ := hex
    intro C D k l
    exact maximality Q closed f g hne hfg k l

/-- Equivalent raw formulation, with the book's generated equality included. -/
theorem raw_maximality (Q : RawProofCongruence P) (closed : Q.Closed)
    {A B : Formula P} (f g : Term P A B) (hne : ¬ Derives f g) (hfg : Q.Rel f g) :
    ∀ {C D} (k l : Term P C D), Q.Rel k l := by
  have he : ofTerm f ≠ ofTerm g := by
    intro h
    exact hne (@Quotient.exact _ (termSetoid A B) _ _ h)
  have ht : Q.toQuotient.Total := maximality Q.toQuotient (Q.toQuotient_closed closed) (ofTerm f) (ofTerm g) he hfg
  intro C D k l
  exact ht (ofTerm k) (ofTerm l)

end DosenPetric.Presentation
