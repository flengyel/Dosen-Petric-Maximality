module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    PositionalCut.rank (P:=Empty)
      (G.disjR [] [] [] .top .bot (G.thinR [] [.top] [] .bot G.topI)) (.here (.disj .top .bot) [])
      (G.disjL G.topIdentity G.botIdentity) (.here (.disj .top .bot) []) = 1 := by
  have hf : (G.disjR [] [] [] .top .bot (G.thinR [] [.top] [] .bot (G.topI (P:=Empty)))).rho
      .right (.here (.disj .top .bot) []) = 1 := G.rho_disjR_principal [] [] [] .top .bot _
  have hg : (G.disjL (G.topIdentity (P:=Empty)) G.botIdentity).rho
      .left (.here (.disj .top .bot) []) = 1 := G.rho_disjL_principal _ _
  unfold PositionalCut.rank
  rw [hf,hg]
  rfl
