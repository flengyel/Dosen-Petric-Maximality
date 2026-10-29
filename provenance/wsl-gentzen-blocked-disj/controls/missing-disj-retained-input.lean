module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example (k : G Empty [.bot,.top] [.top]) (g : G Empty [.top] [.top]) :
    G Empty [.disj .top .top,.bot] [.top,.top] := G.disjL k g
