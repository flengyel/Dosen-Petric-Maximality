module

public import DosenPetric.PresentationNormalizationTerms

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}

theorem ofTerm_cast {A B C D : NormalForm P} (hA : A = C) (hB : B = D) (f : Term P A B) :
    ofTerm (f.cast hA hB) = castHom hA hB (ofTerm f) := by
  cases hA; cases hB; rfl

end DosenPetric.Reduced
namespace DosenPetric.Presentation
universe u
variable {P : Type u}
open NegationNormalization (forwardTerm backwardTerm form_true)

/-- Derived negation expressed entirely in the primitive source grammar. -/
def Term.negate {A B : Formula P} (f : Term P A B) : Term P (.neg B) (.neg A) :=
  .comp (forwardTerm (.neg B) false)
    (.comp (((Reduced.red f).dual.cast (form_true B).symm (form_true A).symm).toFull)
      (backwardTerm (.neg A) false))

theorem negateTerm_denotes {A B : Formula P} (f : Term P A B) :
    ofTerm f.negate = negate (ofTerm f) := by
  change comp (ofTerm (forwardTerm (.neg B) false))
    (comp (Reduced.inclusion (Reduced.ofTerm ((Reduced.red f).dual.cast _ _)))
      (ofTerm (backwardTerm (.neg A) false))) = _
  rw [NegationNormalization.forwardTerm_denotes,NegationNormalization.backwardTerm_denotes,
    Reduced.ofTerm_cast]
  rfl

theorem negate_derives {A B : Formula P} {f g : Term P A B} (h : Derives f g) :
    Derives f.negate g.negate := by
  have he : ofTerm f.negate = ofTerm g.negate := by
    rw [negateTerm_denotes,negateTerm_denotes,sound h]
  exact @Quotient.exact _ (termSetoid (.neg B) (.neg A)) _ _ he

end DosenPetric.Presentation
