module

public import DosenPetric.GentzenSameSideExchangeFixedRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W1.SameSideExchange
universe u
variable {P : Type u}

/-- Proved output laws, never assumptions required of a concrete coordinate construction. -/
structure LeftLaws (d : GapExchange.Data P) (hn : 2 ≤ d.gs0.length)
    (Δ : List (NormalForm P)) (f : G P d.U0 Δ) : Prop where
  denote : ofTerm (newL d hn Δ f).denote = ofTerm (oldL d hn Δ f).denote
  cutCount : (newL d hn Δ f).cutCount = (oldL d hn Δ f).cutCount
  cutFree : (newL d hn Δ f).CutFree ↔ (oldL d hn Δ f).CutFree
  atomized : (newL d hn Δ f).Atomized ↔ (oldL d hn Δ f).Atomized
  new_atomized : (newL d hn Δ f).Atomized ↔ f.Atomized
  old_atomized : (oldL d hn Δ f).Atomized ↔ f.Atomized
  relation : (newL d hn Δ f).relation = (oldL d hn Δ f).relation
  contraction_loss : rankOldL d hn Δ f = rankNewL d hn Δ f + d.gs0.length
  old_rank : (oldL d hn Δ f).rho .left d.keep1 = rankOldL d hn Δ f
  endpoint_rank : (newL d hn Δ f).rho .left d.keep1 = rankNewL d hn Δ f + 1
  endpoint_loss : (oldL d hn Δ f).rho .left d.keep1 + 1 = (newL d hn Δ f).rho .left d.keep1 + d.gs0.length
  contraction_decreases : rankNewL d hn Δ f < rankOldL d hn Δ f
  endpoint_decreases : (newL d hn Δ f).rho .left d.keep1 < (oldL d hn Δ f).rho .left d.keep1
  fixed_old : ∀ {A : NormalForm P} (a : At d.K0 A) (ha : a.index ≠ d.keep0.index),
    (oldL d hn Δ f).rho .left (d.swapLower a) = 2 + f.rho .left (d.fixed0 a ha)
  fixed_new : ∀ {A : NormalForm P} (a : At d.K0 A) (ha : a.index ≠ d.keep0.index),
    (newL d hn Δ f).rho .left (d.swapLower a) = 2 + f.rho .left (d.fixed0 a ha)

/-- Proved output laws, never assumptions required of a concrete coordinate construction. -/
structure RightLaws (d : GapExchange.Data P) (hn : 2 ≤ d.gs0.length)
    (Γ : List (NormalForm P)) (f : G P Γ d.U0) : Prop where
  denote : ofTerm (newR d hn Γ f).denote = ofTerm (oldR d hn Γ f).denote
  cutCount : (newR d hn Γ f).cutCount = (oldR d hn Γ f).cutCount
  cutFree : (newR d hn Γ f).CutFree ↔ (oldR d hn Γ f).CutFree
  atomized : (newR d hn Γ f).Atomized ↔ (oldR d hn Γ f).Atomized
  new_atomized : (newR d hn Γ f).Atomized ↔ f.Atomized
  old_atomized : (oldR d hn Γ f).Atomized ↔ f.Atomized
  relation : (newR d hn Γ f).relation = (oldR d hn Γ f).relation
  contraction_loss : rankOldR d hn Γ f = rankNewR d hn Γ f + d.gs0.length
  old_rank : (oldR d hn Γ f).rho .right d.keep1 = rankOldR d hn Γ f
  endpoint_rank : (newR d hn Γ f).rho .right d.keep1 = rankNewR d hn Γ f + 1
  endpoint_loss : (oldR d hn Γ f).rho .right d.keep1 + 1 = (newR d hn Γ f).rho .right d.keep1 + d.gs0.length
  contraction_decreases : rankNewR d hn Γ f < rankOldR d hn Γ f
  endpoint_decreases : (newR d hn Γ f).rho .right d.keep1 < (oldR d hn Γ f).rho .right d.keep1
  fixed_old : ∀ {A : NormalForm P} (a : At d.K0 A) (ha : a.index ≠ d.keep0.index),
    (oldR d hn Γ f).rho .right (d.swapLower a) = 2 + f.rho .right (d.fixed0 a ha)
  fixed_new : ∀ {A : NormalForm P} (a : At d.K0 A) (ha : a.index ≠ d.keep0.index),
    (newR d hn Γ f).rho .right (d.swapLower a) = 2 + f.rho .right (d.fixed0 a ha)

theorem leftLaws (d : GapExchange.Data P) (hn : 2 ≤ d.gs0.length)
    (Δ : List (NormalForm P)) (f : G P d.U0 Δ) : LeftLaws d hn Δ f :=
  ⟨denoteL ..,cutCountL ..,cutFreeL ..,atomizedL ..,newL_atomized_iff ..,
    oldL_atomized_iff ..,relationL ..,contraction_lossL ..,oldL_rank ..,endpoint_rankL ..,
    endpoint_lossL ..,contraction_decreasesL ..,endpoint_decreasesL ..,
    (fun a ha => fixed_oldL_rank d hn Δ f a ha),
    (fun a ha => fixed_newL_rank d hn Δ f a ha)⟩

theorem rightLaws (d : GapExchange.Data P) (hn : 2 ≤ d.gs0.length)
    (Γ : List (NormalForm P)) (f : G P Γ d.U0) : RightLaws d hn Γ f :=
  ⟨denoteR ..,cutCountR ..,cutFreeR ..,atomizedR ..,newR_atomized_iff ..,
    oldR_atomized_iff ..,relationR ..,contraction_lossR ..,oldR_rank ..,endpoint_rankR ..,
    endpoint_lossR ..,contraction_decreasesR ..,endpoint_decreasesR ..,
    (fun a ha => fixed_oldR_rank d hn Γ f a ha),
    (fun a ha => fixed_newR_rank d hn Γ f a ha)⟩

theorem interior_left (C : NormalForm P) (pre post : List (List (NormalForm P)))
    (U X Y V Θ Δ : List (NormalForm P))
    (hn : 2 ≤ (pre ++ (U ++ X ++ Y ++ V) :: post).length) (f : G P ((repeated C pre ++ U) ++ X ++ Y ++ (V ++ C :: (repeated C post ++ Θ))) Δ) :
    LeftLaws (GapExchange.interior C pre post U X Y V Θ) hn Δ f := leftLaws ..

theorem interior_right (C : NormalForm P) (pre post : List (List (NormalForm P)))
    (U X Y V Θ Γ : List (NormalForm P))
    (hn : 2 ≤ (pre ++ (U ++ X ++ Y ++ V) :: post).length) (f : G P Γ ((repeated C pre ++ U) ++ X ++ Y ++ (V ++ C :: (repeated C post ++ Θ)))) :
    RightLaws (GapExchange.interior C pre post U X Y V Θ) hn Γ f := rightLaws ..

theorem terminal_left (C : NormalForm P) (gs : List (List (NormalForm P)))
    (U X Y V Δ : List (NormalForm P))
    (hn : 2 ≤ gs.length) (f : G P ((repeated C gs ++ U) ++ X ++ Y ++ V) Δ) :
    LeftLaws (GapExchange.terminal C gs U X Y V) hn Δ f := leftLaws ..

theorem terminal_right (C : NormalForm P) (gs : List (List (NormalForm P)))
    (U X Y V Γ : List (NormalForm P))
    (hn : 2 ≤ gs.length) (f : G P Γ ((repeated C gs ++ U) ++ X ++ Y ++ V)) :
    RightLaws (GapExchange.terminal C gs U X Y V) hn Γ f := rightLaws ..

end DosenPetric.Reduced.Gentzen.W1.SameSideExchange
