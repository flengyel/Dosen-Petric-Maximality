module

public import DosenPetric.GentzenDistributiveRepresentation

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Exhaustive induction on the actual nineteen eta/epsilon-free schemas. -/
theorem positive_represented {A B : NormalForm P} (t : Term P A B) (h : t.Positive) :
    Represented (ofTerm t) := by
  induction h with
  | id A => exact Represented.identity A
  | comp _ _ ih ih' => exact ih.comp ih'
  | tensor o _ _ ih ih' => exact ih.tensor o ih'
  | assocR o A B C => exact Represented.assocR o A B C
  | assocL o A B C => exact Represented.assocL o A B C
  | swap o A B => exact Represented.swap o A B
  | diag A => exact Represented.diag A
  | codiag A => exact Represented.codiag A
  | fst A B => exact Represented.fst A B
  | snd A B => exact Represented.snd A B
  | inl A B => exact Represented.inl A B
  | inr A B => exact Represented.inr A B
  | rightOut o A => exact Represented.rightOut o A
  | rightIn o A => exact Represented.rightIn o A
  | leftOut o A => exact Represented.leftOut o A
  | leftIn o A => exact Represented.leftIn o A
  | mix A B => exact Represented.mix A B
  | dist A B C => exact Represented.dist A B C
  | zero A => exact Represented.zero A

/-- Existential Gentzenization with the explicit singleton unit comparisons. -/
theorem gentzenization {A B : NormalForm P} (t : Term P A B) (h : t.Positive) :
    ∃ g : G P [A] [B], ofTerm g.denote =
      comp (rightOut .conj A) (comp (ofTerm t) (rightIn .disj B)) := by
  obtain ⟨g, hg⟩ := positive_represented t h
  exact ⟨g, (denote_value g).trans (congrArg (fun f =>
    comp (rightOut .conj A) (comp f (rightIn .disj B))) hg)⟩

/-- Equivalent representation directly at the original formula endpoints. -/
theorem gentzenization_decode {A B : NormalForm P} (t : Term P A B) (h : t.Positive) :
    ∃ g : G P [A] [B],
      comp (rightIn .conj A) (comp (ofTerm g.denote) (rightOut .disj B)) = ofTerm t :=
  positive_represented t h

end DosenPetric.Reduced.Gentzen
