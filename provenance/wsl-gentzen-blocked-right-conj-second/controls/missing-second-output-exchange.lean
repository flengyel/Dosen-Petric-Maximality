module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example (f : G Empty [] [.top,.top]) (k : G Empty [] [.top,.bot]) :
    G Empty [] [.top,.conj .top .bot,.top] :=
   G.conjR f ((HeadRouting.front [.top] [] .bot).right k)
