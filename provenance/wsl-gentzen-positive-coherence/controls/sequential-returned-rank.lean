module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    (G.conjL [] [] [.top] .top .top (G.thinL [] [.top] [.top] .top (G.topIdentity (P:=Empty)))).rho
      .left (.here (.conj .top .top) []) =
      (G.thinL [] [.top] [.top] .top (G.topIdentity (P:=Empty))).rho .left (.here .top [.top])+1 := by
  have hf : (G.conjL [] [] [.top] .top .top
      (G.thinL [] [.top] [.top] .top (G.topIdentity (P:=Empty)))).rho .left (.here (.conj .top .top) []) = 1 :=
    G.rho_conjL_principal [] [] [.top] .top .top _
  have hk : (G.thinL [] [.top] [.top] .top (G.topIdentity (P:=Empty))).rho .left (.here .top [.top]) = 1 :=
    G.rho_thinL_principal [] [.top] [.top] .top _
  rw [hf,hk]
  rfl
