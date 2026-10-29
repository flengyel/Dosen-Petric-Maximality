module

public import DosenPetric.GentzenNormalExpansion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Positive represented arrows at arbitrary endpoints are determined by their
complete occurrence relations. The expansions require only one-sided recovery. -/
theorem represented_coherence {A B : NormalForm P} (f g : Hom A B)
    (hf : Represented f) (hg : Represented g) (h : occurrenceMap f = occurrenceMap g) : f = g := by
  obtain ⟨D,r,hD⟩ := dnf_expansion A
  obtain ⟨C,s,hC⟩ := cnf_expansion B
  have rf : Represented (comp r.backward (comp f s.forward)) :=
    r.backward_represented.comp (hf.comp s.forward_represented)
  have rg : Represented (comp r.backward (comp g s.forward)) :=
    r.backward_represented.comp (hg.comp s.forward_represented)
  have hr : occurrenceMap (comp r.backward (comp f s.forward)) =
      occurrenceMap (comp r.backward (comp g s.forward)) := by
    simp only [occurrence_comp,h]
  have hc := normal_represented_coherence hD hC _ _ rf rg hr
  apply cancel_left f g r.backward r.forward r.recover
  apply cancel_right (comp r.backward f) (comp r.backward g) s.forward s.backward s.recover
  simpa only [Laws.assoc] using hc

/-- The formerly unsupplied eta/epsilon-free coherence input is now proved. -/
theorem positive_coherence : PositiveCoherence P := by
  intro A B f g hf hg h
  exact represented_coherence (ofTerm f) (ofTerm g)
    (positive_represented f hf) (positive_represented g hg) h

end DosenPetric.Reduced.Gentzen
