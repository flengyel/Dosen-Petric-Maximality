module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example : Presentation.occurrenceMap
    (Presentation.substitute (fun _ : Nat => (Formula.conj (.var 0) (.var 0) : Formula Nat))
      (Presentation.id (.var 0))) (Sum.inl ()) (Sum.inr ()) := by rfl
