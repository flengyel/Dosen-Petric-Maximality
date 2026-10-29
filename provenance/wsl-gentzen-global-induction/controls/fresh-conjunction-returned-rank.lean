module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    (SequentialConjFirst.fresh (P:=Empty) (Γ:=[.bot]) (Θ:=[]) (I:=[]) (J:=[]) (F:=[.top]) (U:=[])
      (G.thinR [.bot] [] [.top] .top (G.thinR [.bot] [] [] .top G.botE)) G.topI).rho
      .right (.here (.conj .top .top) [.top]) = 2 := by
  have hf : (SequentialConjFirst.fresh (P:=Empty) (Γ:=[.bot]) (Θ:=[]) (I:=[]) (J:=[]) (F:=[.top]) (U:=[])
      (G.thinR [.bot] [] [.top] .top (G.thinR [.bot] [] [] .top G.botE)) G.topI).rho
      .right (.here (.conj .top .top) [.top]) = 1 := G.rho_conjR_principal _ _
  rw [hf]
  rfl
