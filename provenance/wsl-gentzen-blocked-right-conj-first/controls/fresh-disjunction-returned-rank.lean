module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    (G.disjR [.top] [] [] .top .top (G.thinR [.top] [] [.top] .top (G.topIdentity (P:=Empty)))).rho
      .right (.here (.disj .top .top) []) =
      (G.thinR [.top] [] [.top] .top (G.topIdentity (P:=Empty))).rho .right (.here .top [.top])+1 := by
  have hf : (G.disjR [.top] [] [] .top .top
      (G.thinR [.top] [] [.top] .top (G.topIdentity (P:=Empty)))).rho .right (.here (.disj .top .top) []) = 1 :=
    G.rho_disjR_principal [.top] [] [] .top .top _
  have hk : (G.thinR [.top] [] [.top] .top (G.topIdentity (P:=Empty))).rho .right (.here .top [.top]) = 1 :=
    G.rho_thinR_principal [.top] [] [.top] .top _
  rw [hf,hk]
  rfl
