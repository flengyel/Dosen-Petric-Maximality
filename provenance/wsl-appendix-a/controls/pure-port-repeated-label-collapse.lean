module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example (l : Literal Nat) :
    (PurePort.left (.lit l) (PurePort.here l) : PurePort .conj (.conj (.lit l) (.lit l)) l).position =
    (PurePort.right (.lit l) (PurePort.here l) : PurePort .conj (.conj (.lit l) (.lit l)) l).position := by rfl
