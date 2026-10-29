module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example (k : G Empty [.top] [.top,.bot]) (g : G Empty [.top] [.top,.top]) :
   G Empty [.top,.top] [.conj .top .top,.top,.bot] := G.conjR k g
