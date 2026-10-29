module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example (l : Literal Nat) :
    (Term.fst (.lit l) (.lit l)).dual = Term.inr (.lit l.flip) (.lit l.flip) := by rfl
