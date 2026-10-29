module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {X : Type} {C : Category X} {O : PresentationSemantics.Objects X}
    {S : PresentationSemantics.Primitives C O} (M : PresentationSemantics.Model Nat S) (α : Nat → X)
    {A B : Formula Nat} (f : Presentation.Hom A B) :
    C.Hom (PresentationSemantics.formula O α B) (PresentationSemantics.formula O α A) :=
  S.evaluateHom M.equations α f
