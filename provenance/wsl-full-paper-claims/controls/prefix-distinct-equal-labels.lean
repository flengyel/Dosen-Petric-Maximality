module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    (SequentialRepair.headRoute (P:=Empty) [.top] [.top]).get
      (.there (.there (.here .top []))) = .here .top [.top] := by rfl
