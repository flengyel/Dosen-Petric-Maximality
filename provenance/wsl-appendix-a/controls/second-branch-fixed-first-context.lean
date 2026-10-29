module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    (BlockedDisjSecond.block (.bot : NormalForm Empty) .top [.disj .bot .top] [] []).route.get
      (.here (.disj .bot .top) [.disj .bot .top,.disj .bot .top]) =
        (BlockedDisjSecond.block .bot .top [.disj .bot .top] [] []).keep := by rfl
