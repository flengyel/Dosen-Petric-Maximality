module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    (Formula.expand (fun p : Nat => Formula.var p) (Formula.conj (.var 0) (.var 0)) (Sum.inl ())).1 =
    (Formula.expand (fun p : Nat => Formula.var p) (Formula.conj (.var 0) (.var 0)) (Sum.inr ())).1 := by rfl
