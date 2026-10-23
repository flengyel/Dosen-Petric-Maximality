module

public import DosenPetric.GentzenSameSideLogicalFixedRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W1.SameSideLogical
universe u
variable {P : Type u}

/-- Output theorems for a concrete construction, not additional inputs to it. -/
structure LeftLaws (d : GapLogical.Data P .conj) (hn : 2 ≤ d.gs0.length)
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
  principal_old : (oldL d hn Δ f).rho .left d.zLower = 2
  principal_new : (newL d hn Δ f).rho .left d.zLower = 1
  other_old : ∀ {E : NormalForm P} (z : At d.K1 E)
    (hp : z.index ≠ d.loBefore.length) (hk : z.index ≠ d.keep1.index),
    (oldL d hn Δ f).rho .left z = 2 + f.rho .left (d.otherUpper z hp hk)
  other_new : ∀ {E : NormalForm P} (z : At d.K1 E)
    (hp : z.index ≠ d.loBefore.length) (hk : z.index ≠ d.keep1.index),
    (newL d hn Δ f).rho .left z = 2 + f.rho .left (d.otherUpper z hp hk)

/-- Output theorems for a concrete construction, not additional inputs to it. -/
structure RightLaws (d : GapLogical.Data P .disj) (hn : 2 ≤ d.gs0.length)
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
  principal_old : (oldR d hn Γ f).rho .right d.zLower = 2
  principal_new : (newR d hn Γ f).rho .right d.zLower = 1
  other_old : ∀ {E : NormalForm P} (z : At d.K1 E)
    (hp : z.index ≠ d.loBefore.length) (hk : z.index ≠ d.keep1.index),
    (oldR d hn Γ f).rho .right z = 2 + f.rho .right (d.otherUpper z hp hk)
  other_new : ∀ {E : NormalForm P} (z : At d.K1 E)
    (hp : z.index ≠ d.loBefore.length) (hk : z.index ≠ d.keep1.index),
    (newR d hn Γ f).rho .right z = 2 + f.rho .right (d.otherUpper z hp hk)

theorem leftLaws (d : GapLogical.Data P .conj) (hn : 2 ≤ d.gs0.length)
    (Δ : List (NormalForm P)) (f : G P d.U0 Δ) : LeftLaws d hn Δ f :=
  ⟨denoteL ..,cutCountL ..,cutFreeL ..,atomizedL ..,newL_atomized_iff ..,
    oldL_atomized_iff ..,relationL ..,contraction_lossL ..,oldL_rank ..,endpoint_rankL ..,
    endpoint_lossL ..,contraction_decreasesL ..,endpoint_decreasesL ..,
    principal_oldL_rank ..,principal_newL_rank ..,
    (fun z hp hk => other_oldL_rank d hn Δ f z hp hk),
    (fun z hp hk => other_newL_rank d hn Δ f z hp hk)⟩

theorem rightLaws (d : GapLogical.Data P .disj) (hn : 2 ≤ d.gs0.length)
    (Γ : List (NormalForm P)) (f : G P Γ d.U0) : RightLaws d hn Γ f :=
  ⟨denoteR ..,cutCountR ..,cutFreeR ..,atomizedR ..,newR_atomized_iff ..,
    oldR_atomized_iff ..,relationR ..,contraction_lossR ..,oldR_rank ..,endpoint_rankR ..,
    endpoint_lossR ..,contraction_decreasesR ..,endpoint_decreasesR ..,
    principal_oldR_rank ..,principal_newR_rank ..,
    (fun z hp hk => other_oldR_rank d hn Γ f z hp hk),
    (fun z hp hk => other_newR_rank d hn Γ f z hp hk)⟩

theorem interior_left (A B C : NormalForm P) (pre post : List (List (NormalForm P)))
    (U V Θ Δ : List (NormalForm P))
    (hn : 2 ≤ (pre ++ (U ++ A :: B :: V) :: post).length) (f : G P ((repeated C pre ++ U) ++ A :: B :: (V ++ C :: (repeated C post ++ Θ))) Δ) :
    LeftLaws (GapLogical.interior .conj A B C pre post U V Θ) hn Δ f := leftLaws ..

theorem interior_right (A B C : NormalForm P) (pre post : List (List (NormalForm P)))
    (U V Θ Γ : List (NormalForm P))
    (hn : 2 ≤ (pre ++ (U ++ A :: B :: V) :: post).length) (f : G P Γ ((repeated C pre ++ U) ++ A :: B :: (V ++ C :: (repeated C post ++ Θ)))) :
    RightLaws (GapLogical.interior .disj A B C pre post U V Θ) hn Γ f := rightLaws ..

theorem terminal_left (A B C : NormalForm P) (gs : List (List (NormalForm P)))
    (U V Δ : List (NormalForm P))
    (hn : 2 ≤ gs.length) (f : G P ((repeated C gs ++ U) ++ A :: B :: V) Δ) :
    LeftLaws (GapLogical.terminal .conj A B C gs U V) hn Δ f := leftLaws ..

theorem terminal_right (A B C : NormalForm P) (gs : List (List (NormalForm P)))
    (U V Γ : List (NormalForm P))
    (hn : 2 ≤ gs.length) (f : G P Γ ((repeated C gs ++ U) ++ A :: B :: V)) :
    RightLaws (GapLogical.terminal .disj A B C gs U V) hn Γ f := rightLaws ..

end DosenPetric.Reduced.Gentzen.W1.SameSideLogical
