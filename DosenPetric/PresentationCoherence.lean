module

public import DosenPetric.ReducedCoherence
public import DosenPetric.PresentationInstances

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Presentation
universe u
variable {P : Type u}

/-- Boolean coherence for the actual equation-generated source category. -/
theorem coherence {A B : Formula P} {f g : Hom A B}
    (h : occurrenceMap f = occurrenceMap g) : f = g := Reduced.boolean_coherence h

/-- The full occurrence interface is instantiated in the intended presentation. -/
def interpretation (P : Type u) : OccurrenceInterpretation (operations P) (zeroIdentity P) where
  map := occurrenceMap
  faithful := coherence
  map_id := occurrence_id
  map_comp := occurrence_comp
  map_fst := occurrence_fst
  map_snd := occurrence_snd
  map_pair := occurrence_pair
  map_inl := occurrence_inl
  map_inr := occurrence_inr
  map_copair := occurrence_copair
  map_zero := occurrence_zero
  map_dist := occurrence_dist

/-- The intended faithful interpretation retains the proved signed-literal invariant. -/
theorem interpretation_signedLabel (P : Type u) : SignedLabelPreservation (interpretation P) := by
  intro A B f x y h
  exact occurrence_literal A B f x y h

end DosenPetric.Presentation
