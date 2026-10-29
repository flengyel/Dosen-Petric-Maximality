module

public import DosenPetric.GentzenPositiveCoherence
public import DosenPetric.CommonAtomicFactorization

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}

/-- Common atomic factorization now discharges the full Reduced coherence input. -/
theorem faithful : Faithful P := faithful_of_positive_coherence Gentzen.positive_coherence

/-- Faithfulness transfers through the proved normal-form representation and
the explicit inverse normalization arrows of the original presentation. -/
theorem boolean_coherence {A B : Formula P} {f g : Presentation.Hom A B}
    (h : Presentation.occurrenceMap f = Presentation.occurrenceMap g) : f = g :=
  global_faithful_of_reduced faithful h

end DosenPetric.Reduced
