module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example (k : G Empty [.bot] [.top]) (g : G Empty [.top] [.top]) :
   G Empty [.bot,.top] [.top,.top] := G.mix k g
