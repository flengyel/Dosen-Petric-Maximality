module

public import DosenPetric.PresentationMaximality

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Presentation
universe u
variable {P : Type u}

/-- The proved isolation and collapse argument needs only the bicartesian
fragment congruence and its uniform substitution closure. -/
theorem fragment_maximality (Q : Congruence (operations P))
    (closed : (substitution P).Closed Q) {A B : Formula P}
    (f g : Hom A B) (hne : f ≠ g) (hfg : Q.Rel f g) : Q.Total :=
  relative_maximality (interpretation P) (normalization P) (interpretation_signedLabel P)
    (substitution P) (doubleNegation P) Q closed f g hne hfg

theorem fragment_dichotomy (Q : Congruence (operations P))
    (closed : (substitution P).Closed Q) :
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
    exact fragment_maximality Q closed f g hne hfg k l

/-- Equality and total relations respect every operation. The previously proved
fragment dichotomy therefore supplies full closure, including derived negation. -/
def ProofCongruence.of_closed_fragment (Q : Congruence (operations P))
    (closed : (substitution P).Closed Q) : ProofCongruence P where
  Rel := Q.Rel
  refl := Q.refl
  symm := Q.symm
  trans := Q.trans
  comp := Q.comp
  tensor o {A B C D f f' g g'} hf hg := by
    cases fragment_dichotomy Q closed with
    | inl he =>
      have hff := (he f f').mp hf
      have hgg := (he g g').mp hg
      cases hff
      cases hgg
      exact Q.refl _
    | inr ht => exact ht _ _
  negate {A B f g} hf := by
    cases fragment_dichotomy Q closed with
    | inl he =>
      have hff := (he f g).mp hf
      cases hff
      exact Q.refl _
    | inr ht => exact ht _ _

theorem ProofCongruence.of_closed_fragment_closed (Q : Congruence (operations P))
    (closed : (substitution P).Closed Q) : (ProofCongruence.of_closed_fragment Q closed).Closed :=
  closed

end DosenPetric.Presentation
