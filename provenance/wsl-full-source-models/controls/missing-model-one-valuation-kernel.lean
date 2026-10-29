module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {X : Type} {C : Category X} {O : PresentationSemantics.Objects X}
    {S : PresentationSemantics.Primitives C O} (M : PresentationSemantics.Model Nat S)
    {A B : Formula Nat} (f g : Presentation.Hom A B) (hne : f ≠ g) (α : Nat → X)
    (h : S.evaluateHom M.equations α f = S.evaluateHom M.equations α g) :
    ∀ {Y Z : X} (a b : C.Hom Y Z), a = b := PresentationSemantics.model_corollary M f g hne h
