module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example (k : G Empty [.top] [.top,.bot]) (l : G Empty [.top] [.top,.bot]) :
    G Empty [.top,.top] [.top,.top,.bot] := G.mix k l
