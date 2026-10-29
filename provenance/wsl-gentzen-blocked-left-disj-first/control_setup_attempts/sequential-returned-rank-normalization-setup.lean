module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    (G.conjL [] [] [.top] .top .top (G.thinL [] [.top] [.top] .top (G.topIdentity (P:=Empty)))).rho
      .left (.here (.conj .top .top) []) =
      (G.thinL [] [.top] [.top] .top (G.topIdentity (P:=Empty))).rho .left (.here .top [.top])+1 := by
  rw [G.rho_conjL_principal,G.rho_thinL_principal]
  rfl
