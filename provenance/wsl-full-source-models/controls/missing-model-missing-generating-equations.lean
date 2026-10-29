module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {X : Type} {C : Category X} {O : PresentationSemantics.Objects X}
    {S : PresentationSemantics.Primitives C O} (α : Nat → X) :
    Functor (Presentation.category Nat) C := S.evaluationFunctor True.intro α
