module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example (k : G Empty [] [.top,.bot]) (g : G Empty [] [.top]) :
   G Empty [] [.conj .bot .top,.top] := G.conjR k g
