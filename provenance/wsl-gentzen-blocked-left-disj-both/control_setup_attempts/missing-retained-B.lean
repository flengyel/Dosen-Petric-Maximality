module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example (f : G Empty [.top] [.top]) (k : G Empty [.bot] [.bot]) :
   G Empty [.top,.bot] [.conj .top .top] := G.conjR f k
