module

public import DosenPetric.GentzenBlockedConjBothRank
public import DosenPetric.GentzenBlockedRightGammaMix
public import DosenPetric.GentzenBlockedGammaDisj

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionBlock

theorem lowerR {U K Γ : List (NormalForm P)} (d : ContractionBlock P U K)
    (hn : 2 ≤ d.gs.length) (f : G P Γ U) : (d.applyR hn Γ f).LowerContraction .right d.keep := by
  rcases d with ⟨C,gs,T,hu,hk⟩
  cases hu
  cases hk
  exact G.LowerContraction.right ..

theorem lowerL {U K Δ : List (NormalForm P)} (d : ContractionBlock P U K)
    (hn : 2 ≤ d.gs.length) (f : G P U Δ) : (d.applyL hn Δ f).LowerContraction .left d.keep := by
  rcases d with ⟨C,gs,T,hu,hk⟩
  cases hu
  cases hk
  exact G.LowerContraction.left ..

end ContractionBlock
namespace CutCommutation

theorem blocked_right_rank_step {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hb : BlockedR f) (hx : f.LowerContraction .right x) (hc : PositionalCut.Clean f x g y)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C), PositionalCut.rank b v d w < PositionalCut.rank f x g y →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated f x g y := by
  cases hb with
  | gammaMix D Γ Θ X Y Z T f h =>
    have hx0 : (BlockedMix.gammaRightParent f h).LowerContraction .right (BlockedMix.gammaBlock D X Y Z T).keep :=
      (BlockedMix.gammaBlock D X Y Z T).lowerR (Nat.le_refl 2) (G.mix f h)
    rw [BlockedMix.gammaRightParent_source] at hx0
    have hi := G.lowerContraction_index_unique _ .right x (BlockedMix.gammaBlock D X Y Z T).keep hx hx0
    cases he : At.compare x (BlockedMix.gammaBlock D X Y Z T).keep with
    | apart hn => exact False.elim (hn hi)
    | same =>
      simpa only [BlockedMix.gammaRightParent_source] using
        blockedR_gammaMix_rank_step f h g y
          (by simpa only [BlockedMix.gammaRightParent_source] using hc)
          (by
            intro K L M N b v d w hr hc'
            exact ih b v d w (by simpa only [BlockedMix.gammaRightParent_source] using hr) hc')
  | gammaDisj D A B Γ Θ X Y Z T f h =>
    have hx0 : (BlockedDisj.gammaParent f h).LowerContraction .right (BlockedMix.gammaBlock D Z T X Y).keep :=
      (BlockedMix.gammaBlock D Z T X Y).lowerR (Nat.le_refl 2) (BlockedSource.disjLLast f h)
    rw [BlockedDisj.gammaParent_source] at hx0
    have hi := G.lowerContraction_index_unique _ .right x (BlockedMix.gammaBlock D Z T X Y).keep hx hx0
    cases he : At.compare x (BlockedMix.gammaBlock D Z T X Y).keep with
    | apart hn => exact False.elim (hn hi)
    | same =>
      simpa only [BlockedDisj.gammaParent_source] using
        blockedR_gammaDisj_rank_step f h g y
          (by simpa only [BlockedDisj.gammaParent_source] using hc)
          (by
            intro K L M N b v d w hr hc'
            exact ih b v d w (by simpa only [BlockedDisj.gammaParent_source] using hr) hc')
  | gammaConj D A B Γ Θ X Y Z T f h =>
    have hx0 : (BlockedRightConj.gammaParent f h).LowerContraction .right (BlockedRightConj.gammaBlock A B D X Y Z T).keep :=
      (BlockedRightConj.gammaBlock A B D X Y Z T).lowerR (Nat.le_refl 2) (G.conjR f h)
    rw [BlockedRightConj.gammaParent_source] at hx0
    have hi := G.lowerContraction_index_unique _ .right x (BlockedRightConj.gammaBlock A B D X Y Z T).keep hx hx0
    cases he : At.compare x (BlockedRightConj.gammaBlock A B D X Y Z T).keep with
    | apart hn => exact False.elim (hn hi)
    | same =>
      simpa only [BlockedRightConj.gammaParent_source,BlockedRightConj.gammaBlock_keep] using
        blockedR_gammaConj_rank_step f h g y
          (by simpa only [BlockedRightConj.gammaParent_source,BlockedRightConj.gammaBlock_keep] using hc)
          (by
            intro K L M N b v d w hr hc'
            exact ih b v d w (by simpa only [BlockedRightConj.gammaParent_source,BlockedRightConj.gammaBlock_keep] using hr) hc')
  | disjunction A B Γ X Y f =>
    have hx0 : (BlockedDisjunction.parent f).LowerContraction .right (BlockedDisjunction.block A B X Y).keep :=
      (BlockedDisjunction.block A B X Y).lowerR (Nat.le_refl 2) (G.disjR Γ [] (X++.disj A B::Y) A B f)
    rw [BlockedDisjunction.parent_source] at hx0
    have hi := G.lowerContraction_index_unique _ .right x (BlockedDisjunction.block A B X Y).keep hx hx0
    cases he : At.compare x (BlockedDisjunction.block A B X Y).keep with
    | apart hn => exact False.elim (hn hi)
    | same =>
      simpa only [BlockedDisjunction.parent_source] using
        blockedR_disjunction_rank_step f g y
          (by simpa only [BlockedDisjunction.parent_source] using hc)
          (by
            intro K L M N b v d w hr hc'
            exact ih b v d w (by simpa only [BlockedDisjunction.parent_source] using hr) hc')
  | conjunctionFirst A B Γ Θ X Y U f h =>
    have hx0 : (BlockedConjFirst.parent f h).LowerContraction .right (BlockedConjFirst.block A B X Y U).keep :=
      (BlockedConjFirst.block A B X Y U).lowerR (Nat.le_refl 2) (G.conjR f h)
    rw [BlockedConjFirst.parent_source] at hx0
    have hi := G.lowerContraction_index_unique _ .right x (BlockedConjFirst.block A B X Y U).keep hx hx0
    cases he : At.compare x (BlockedConjFirst.block A B X Y U).keep with
    | apart hn => exact False.elim (hn hi)
    | same =>
      simpa only [BlockedConjFirst.parent_source] using
        blockedR_conjunctionFirst_rank_step f h g y
          (by simpa only [BlockedConjFirst.parent_source] using hc)
          (by
            intro K L M N b v d w hr hc'
            exact ih b v d w (by simpa only [BlockedConjFirst.parent_source] using hr) hc')
  | conjunctionSecond A B Γ Θ F Z T f h =>
    have hx0 : (BlockedConjSecond.parent f h).LowerContraction .right (BlockedConjSecond.block A B F Z T).keep :=
      (BlockedConjSecond.block A B F Z T).lowerR (Nat.le_refl 2) (G.conjR f h)
    rw [BlockedConjSecond.parent_source] at hx0
    have hi := G.lowerContraction_index_unique _ .right x (BlockedConjSecond.block A B F Z T).keep hx hx0
    cases he : At.compare x (BlockedConjSecond.block A B F Z T).keep with
    | apart hn => exact False.elim (hn hi)
    | same =>
      simpa only [BlockedConjSecond.parent_source] using
        blockedR_conjunctionSecond_rank_step f h g y
          (by simpa only [BlockedConjSecond.parent_source] using hc)
          (by
            intro K L M N b v d w hr hc'
            exact ih b v d w (by simpa only [BlockedConjSecond.parent_source] using hr) hc')
  | conjunctionBoth A B Γ Θ X Y Z T f h =>
    have hx0 : (BlockedConjBoth.parent f h).LowerContraction .right (BlockedConjBoth.block A B X Y Z T).keep :=
      (BlockedConjBoth.block A B X Y Z T).lowerR (Nat.le_succ 2) (G.conjR f h)
    rw [BlockedConjBoth.parent_source] at hx0
    have hi := G.lowerContraction_index_unique _ .right x (BlockedConjBoth.block A B X Y Z T).keep hx hx0
    cases he : At.compare x (BlockedConjBoth.block A B X Y Z T).keep with
    | apart hn => exact False.elim (hn hi)
    | same =>
      simpa only [BlockedConjBoth.parent_source] using
        blockedR_conjunctionBoth_rank_step f h g y
          (by simpa only [BlockedConjBoth.parent_source] using hc)
          (by
            intro K L M N b v d w hr hc'
            exact ih b v d w (by simpa only [BlockedConjBoth.parent_source] using hr) hc')

end CutCommutation
end DosenPetric.Reduced.Gentzen
