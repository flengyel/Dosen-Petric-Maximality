module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example (k : G Empty [.top] [.bot,.top]) (l : G Empty [.top] [.bot,.top]) :
    G Empty [.disj .top .top] [.bot,.top,.top] := BlockedSource.disjLLast k l
