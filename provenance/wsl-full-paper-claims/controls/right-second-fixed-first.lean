module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    (BlockedConjSecond.block (.bot : NormalForm Empty) .top [.conj .bot .top] [] []).route.get
      (.there (.here (.conj .bot .top) [.conj .bot .top])) =
        (BlockedConjSecond.block .bot .top [.conj .bot .top] [] []).keep := by rfl
