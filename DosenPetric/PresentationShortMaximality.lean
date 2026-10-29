module

public import DosenPetric.PresentationShortSubstitution

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation
universe u
variable {P : Type u}

/-- Actual maximality via the manuscript's distinct short q_A/e_A route. -/
theorem short_maximality (Q : ProofCongruence P) (closed : Q.Closed)
    {A B : Formula P} (f g : Hom A B) (hne : f ≠ g) (hfg : Q.Rel f g) : Q.Total := by
  obtain ⟨l,hl⟩ := Isolation.normalized_literal_context (interpretation P) (normalization P)
    (interpretation_signedLabel P) Q.fragment f g hne hfg
  have allK : ∀ C, ContextualCollapse.K Q.fragment (Z := zeroIdentity P) C :=
    ContextualCollapse.all_contexts Q.fragment (substitution P) (doubleNegation P)
      (Q.fragment_closed closed) l hl
  intro C D k l
  exact ShortProof.total Q.fragment allK k l

end DosenPetric.Presentation
