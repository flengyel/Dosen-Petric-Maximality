module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    (G.disjR [.top] [] [] .top .top (G.thinR [.top] [] [.top] .top (G.topIdentity (P:=Empty)))).rho
      .right (.here (.disj .top .top) []) =
      (G.thinR [.top] [] [.top] .top (G.topIdentity (P:=Empty))).rho .right (.here .top [.top])+1 := by rfl
