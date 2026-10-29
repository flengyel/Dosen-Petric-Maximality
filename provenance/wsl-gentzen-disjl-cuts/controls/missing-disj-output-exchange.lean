module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example (k : G Empty [.top] [.top,.bot]) (g : G Empty [.top] [.top]) :
    G Empty [.disj .top .top] [.top,.top,.bot] := G.disjL k g
