module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    (BlockedSource.disjLLast (Γ:=[]) (Θ:=[]) (G.topIdentity (P:=Empty)) G.topIdentity).rho
      .left (.here (.disj .top .top) []) = 1 := by
  have hr : (BlockedSource.disjLLast (Γ:=[]) (Θ:=[]) (G.topIdentity (P:=Empty)) G.topIdentity).rho
      .left (.here (.disj .top .top) []) = 2 := BlockedSource.disjLLast_rank_principal _ _
  rw [hr]
  rfl
