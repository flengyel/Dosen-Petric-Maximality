module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example (k : G Empty [.top] [.top]) (l : G Empty [.top] [.top]) :
    G Empty [.top] [.top,.top] := G.mix k l
