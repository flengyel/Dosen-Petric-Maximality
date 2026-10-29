module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {X : Type} {C : Category X} {O : PresentationSemantics.Objects X}
    {S : PresentationSemantics.Primitives C O} (F : PresentationSemantics.Interpretation S Empty)
    (σ : Nat → Formula Empty) : PresentationSemantics.Interpretation S Empty := F.precompose σ
