module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {P : Type} (A : Formula P)
    (x : (Presentation.NegationNormalization.normal A).formula.Occ) :
    Presentation.Hom (.conj ((Presentation.NegationNormalization.normal A).literalAt x).formula .bot) A :=
  Isolation.selector (Presentation.operations P) (Presentation.NegationNormalization.normal A) x
