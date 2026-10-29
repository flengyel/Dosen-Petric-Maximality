module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example (k : G Empty [.top,.top] [.bot]) (l : G Empty [.top,.top] [.bot]) :
    G Empty [.top,.disj .top .top] [.bot,.bot] := BlockedSource.disjLLast k l
