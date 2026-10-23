module

public import DosenPetric.GentzenSameSideThinningRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace GapInsertion

theorem interior_inserted_before (C E : NormalForm P) (pre post : List (List (NormalForm P)))
    (U V Θ : List (NormalForm P)) :
    (interior C E pre post U V Θ).zLower.index < (interior C E pre post U V Θ).keep1.index := by
  rw [Data.zLower_index,Data.keep1_index]
  simp only [interior, List.length_append, gaps_append, gaps, List.length_cons]
  omega

theorem terminal_inserted_after (C E : NormalForm P) (gs : List (List (NormalForm P)))
    (U V : List (NormalForm P)) :
    (terminal C E gs U V).keep1.index < (terminal C E gs U V).zLower.index := by
  rw [Data.zLower_index,Data.keep1_index]
  simp only [terminal,List.length_append,List.length_cons]
  omega

end GapInsertion

namespace W1.SameSideThinning

/-- The output laws of a concrete left commutation; no law is assumed to construct it. -/
structure LeftLaws (d : GapInsertion.Data P) (hn : 2 ≤ d.gs0.length)
    (Δ : List (NormalForm P)) (f : G P d.U0 Δ) : Prop where
  denote : ofTerm (newL d hn Δ f).denote = ofTerm (oldL d hn Δ f).denote
  cutCount : (newL d hn Δ f).cutCount = (oldL d hn Δ f).cutCount
  cutFree : (newL d hn Δ f).CutFree ↔ (oldL d hn Δ f).CutFree
  atomized : (newL d hn Δ f).Atomized ↔ (oldL d hn Δ f).Atomized
  relation : (newL d hn Δ f).relation = (oldL d hn Δ f).relation
  contraction_loss : rankOldL d hn Δ f = rankNewL d hn Δ f + d.gs0.length
  endpoint_rank : (newL d hn Δ f).rho .left d.keep1 = rankNewL d hn Δ f + 1
  endpoint_loss : (oldL d hn Δ f).rho .left d.keep1 + 1 =
    (newL d hn Δ f).rho .left d.keep1 + d.gs0.length
  contraction_decreases : rankNewL d hn Δ f < rankOldL d hn Δ f
  endpoint_decreases : (newL d hn Δ f).rho .left d.keep1 < (oldL d hn Δ f).rho .left d.keep1
  inserted_old : (oldL d hn Δ f).rho .left d.zLower = 2
  inserted_new : (newL d hn Δ f).rho .left d.zLower = 1

structure RightLaws (d : GapInsertion.Data P) (hn : 2 ≤ d.gs0.length)
    (Γ : List (NormalForm P)) (f : G P Γ d.U0) : Prop where
  denote : ofTerm (newR d hn Γ f).denote = ofTerm (oldR d hn Γ f).denote
  cutCount : (newR d hn Γ f).cutCount = (oldR d hn Γ f).cutCount
  cutFree : (newR d hn Γ f).CutFree ↔ (oldR d hn Γ f).CutFree
  atomized : (newR d hn Γ f).Atomized ↔ (oldR d hn Γ f).Atomized
  relation : (newR d hn Γ f).relation = (oldR d hn Γ f).relation
  contraction_loss : rankOldR d hn Γ f = rankNewR d hn Γ f + d.gs0.length
  endpoint_rank : (newR d hn Γ f).rho .right d.keep1 = rankNewR d hn Γ f + 1
  endpoint_loss : (oldR d hn Γ f).rho .right d.keep1 + 1 =
    (newR d hn Γ f).rho .right d.keep1 + d.gs0.length
  contraction_decreases : rankNewR d hn Γ f < rankOldR d hn Γ f
  endpoint_decreases : (newR d hn Γ f).rho .right d.keep1 < (oldR d hn Γ f).rho .right d.keep1
  inserted_old : (oldR d hn Γ f).rho .right d.zLower = 2
  inserted_new : (newR d hn Γ f).rho .right d.zLower = 1

theorem leftLaws (d : GapInsertion.Data P) (hn : 2 ≤ d.gs0.length)
    (Δ : List (NormalForm P)) (f : G P d.U0 Δ) : LeftLaws d hn Δ f :=
  ⟨denoteL ..,cutCountL ..,cutFreeL ..,atomizedL ..,relationL ..,contraction_lossL ..,
    endpoint_rankL ..,endpoint_lossL ..,contraction_decreasesL ..,endpoint_decreasesL ..,
    inserted_oldL_rank ..,inserted_newL_rank ..⟩

theorem rightLaws (d : GapInsertion.Data P) (hn : 2 ≤ d.gs0.length)
    (Γ : List (NormalForm P)) (f : G P Γ d.U0) : RightLaws d hn Γ f :=
  ⟨denoteR ..,cutCountR ..,cutFreeR ..,atomizedR ..,relationR ..,contraction_lossR ..,
    endpoint_rankR ..,endpoint_lossR ..,contraction_decreasesR ..,endpoint_decreasesR ..,
    inserted_oldR_rank ..,inserted_newR_rank ..⟩

/-- Interior-gap W1 on the antecedent. The result has source d.K1 and target Δ. -/
theorem interior_left (C E : NormalForm P) (pre post : List (List (NormalForm P)))
    (U V Θ Δ : List (NormalForm P)) (hn : 2 ≤ (pre ++ (U ++ V) :: post).length)
    (f : G P ((repeated C pre ++ U) ++ (V ++ C :: (repeated C post ++ Θ))) Δ) :
    LeftLaws (GapInsertion.interior C E pre post U V Θ) hn Δ f := leftLaws ..

theorem interior_right (C E : NormalForm P) (pre post : List (List (NormalForm P)))
    (U V Θ Γ : List (NormalForm P)) (hn : 2 ≤ (pre ++ (U ++ V) :: post).length)
    (f : G P Γ ((repeated C pre ++ U) ++ (V ++ C :: (repeated C post ++ Θ)))) :
    RightLaws (GapInsertion.interior C E pre post U V Θ) hn Γ f := rightLaws ..

/-- Terminal-tail W1; gs is unchanged, including its ordered selected-copy list. -/
theorem terminal_left (C E : NormalForm P) (gs : List (List (NormalForm P)))
    (U V Δ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (f : G P ((repeated C gs ++ U) ++ V) Δ) :
    LeftLaws (GapInsertion.terminal C E gs U V) hn Δ f := leftLaws ..

theorem terminal_right (C E : NormalForm P) (gs : List (List (NormalForm P)))
    (U V Γ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (f : G P Γ ((repeated C gs ++ U) ++ V)) :
    RightLaws (GapInsertion.terminal C E gs U V) hn Γ f := rightLaws ..

end W1.SameSideThinning
end DosenPetric.Reduced.Gentzen
