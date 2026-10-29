module

public import DosenPetric.GentzenPositionalReindex
public import DosenPetric.GentzenBlockedGammaConj
public import DosenPetric.GentzenBlockedLeftGammaDisjRank

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.CutCommutation
universe u
variable {P : Type u}

theorem blocked_left_rank_step {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (h : G P Γ Δ) (z : At Δ C) (g : G P Θ Λ) (x : At Θ C)
    (hb : BlockedL g) (hx : g.LowerContraction .left x) (hc : PositionalCut.Clean h z g x)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C), PositionalCut.rank b v d w < PositionalCut.rank h z g x →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z g x := by
  cases hb with
  | gammaMix D X Y Z T Δ Λ f k =>
    have hx0 : (BlockedMix.gammaParent f k).LowerContraction .left (BlockedMix.gammaBlock D X Y Z T).keep :=
      (BlockedMix.gammaBlock D X Y Z T).lowerL (Nat.le_refl 2) (G.mix f k)
    rw [BlockedMix.gammaParent_source] at hx0
    have hi := G.lowerContraction_index_unique _ .left x (BlockedMix.gammaBlock D X Y Z T).keep hx hx0
    cases he : At.compare x (BlockedMix.gammaBlock D X Y Z T).keep with
    | apart hn => exact False.elim (hn hi)
    | same =>
      simpa only [BlockedMix.gammaParent_source] using
        blockedL_gammaMix_rank_step f k h z
          (by simpa only [BlockedMix.gammaParent_source] using hc)
          (by
            intro K L M N b v d w hr hc'
            exact ih b v d w (by simpa only [BlockedMix.gammaParent_source] using hr) hc')
  | gammaConj D A B X Y Z T Δ Λ f k =>
    have hx0 : (BlockedConj.gammaParent f k).LowerContraction .left (BlockedMix.gammaBlock D Z T X Y).keep :=
      (BlockedMix.gammaBlock D Z T X Y).lowerL (Nat.le_refl 2) (G.conjR f k)
    rw [BlockedConj.gammaParent_source] at hx0
    have hi := G.lowerContraction_index_unique _ .left x (BlockedMix.gammaBlock D Z T X Y).keep hx hx0
    cases he : At.compare x (BlockedMix.gammaBlock D Z T X Y).keep with
    | apart hn => exact False.elim (hn hi)
    | same =>
      simpa only [BlockedConj.gammaParent_source] using
        blockedL_gammaConj_rank_step f k h z
          (by simpa only [BlockedConj.gammaParent_source] using hc)
          (by
            intro K L M N b v d w hr hc'
            exact ih b v d w (by simpa only [BlockedConj.gammaParent_source] using hr) hc')
  | conjunction A B X Y Δ f =>
    have hx0 : (BlockedConjunction.parent f).LowerContraction .left (BlockedConjunction.block A B X Y).keep :=
      (BlockedConjunction.block A B X Y).lowerL (Nat.le_refl 2) (BlockedSource.conjLLast (X++.conj A B::Y) _ A B f)
    rw [BlockedConjunction.parent_source] at hx0
    have hi := G.lowerContraction_index_unique _ .left x (BlockedConjunction.block A B X Y).keep hx hx0
    cases he : At.compare x (BlockedConjunction.block A B X Y).keep with
    | apart hn => exact False.elim (hn hi)
    | same =>
      simpa only [BlockedConjunction.parent_source] using
        blockedL_conjunction_rank_step f h z
          (by simpa only [BlockedConjunction.parent_source] using hc)
          (by
            intro K L M N b v d w hr hc'
            exact ih b v d w (by simpa only [BlockedConjunction.parent_source] using hr) hc')
  | disjunctionFirst A B X Y Z Δ Λ f k =>
    have hx0 : (BlockedDisjFirst.parent f k).LowerContraction .left (BlockedDisjFirst.block A B X Y Z).keep :=
      (BlockedDisjFirst.block A B X Y Z).lowerL (Nat.le_refl 2) (BlockedSource.disjLLast f k)
    rw [BlockedDisjFirst.parent_source] at hx0
    have hi := G.lowerContraction_index_unique _ .left x (BlockedDisjFirst.block A B X Y Z).keep hx hx0
    cases he : At.compare x (BlockedDisjFirst.block A B X Y Z).keep with
    | apart hn => exact False.elim (hn hi)
    | same =>
      simpa only [BlockedDisjFirst.parent_source] using
        blockedL_disjunctionFirst_rank_step f k h z
          (by simpa only [BlockedDisjFirst.parent_source] using hc)
          (by
            intro K L M N b v d w hr hc'
            exact ih b v d w (by simpa only [BlockedDisjFirst.parent_source] using hr) hc')
  | disjunctionSecond A B X Z T Δ Λ f k =>
    have hx0 : (BlockedDisjSecond.parent f k).LowerContraction .left (BlockedDisjSecond.block A B X Z T).keep :=
      (BlockedDisjSecond.block A B X Z T).lowerL (Nat.le_refl 2) (BlockedSource.disjLLast f k)
    rw [BlockedDisjSecond.parent_source] at hx0
    have hi := G.lowerContraction_index_unique _ .left x (BlockedDisjSecond.block A B X Z T).keep hx hx0
    cases he : At.compare x (BlockedDisjSecond.block A B X Z T).keep with
    | apart hn => exact False.elim (hn hi)
    | same =>
      simpa only [BlockedDisjSecond.parent_source] using
        blockedL_disjunctionSecond_rank_step f k h z
          (by simpa only [BlockedDisjSecond.parent_source] using hc)
          (by
            intro K L M N b v d w hr hc'
            exact ih b v d w (by simpa only [BlockedDisjSecond.parent_source] using hr) hc')
  | disjunctionBoth A B X Y Z T Δ Λ f k =>
    have hx0 : (BlockedDisjBoth.parent f k).LowerContraction .left (BlockedDisjBoth.block A B X Y Z T).keep :=
      (BlockedDisjBoth.block A B X Y Z T).lowerL (Nat.le_succ 2) (BlockedSource.disjLLast f k)
    rw [BlockedDisjBoth.parent_source] at hx0
    have hi := G.lowerContraction_index_unique _ .left x (BlockedDisjBoth.block A B X Y Z T).keep hx hx0
    cases he : At.compare x (BlockedDisjBoth.block A B X Y Z T).keep with
    | apart hn => exact False.elim (hn hi)
    | same =>
      simpa only [BlockedDisjBoth.parent_source] using
        blockedL_disjunctionBoth_rank_step f k h z
          (by simpa only [BlockedDisjBoth.parent_source] using hc)
          (by
            intro K L M N b v d w hr hc'
            exact ih b v d w (by simpa only [BlockedDisjBoth.parent_source] using hr) hc')
  | gammaDisj D A B X Y Z T Δ Λ f k =>
    let d := (BlockedMix.gammaBlock D Z T X Y).extend [.disj A B]
    let p := BlockedLeftDisj.gammaParent f k
    let v := (BlockedMix.gammaBlock D Z T X Y).keep.before [.disj A B]
    let e : (gaps [X,Y++Z]++D::T)++[.disj A B] = gaps [X,Y++Z]++D::(T++[.disj A B]) := by
      simp only [List.append_assoc,List.cons_append]
    have hl0 : p.LowerContraction .left v := by
      simpa only [p,BlockedLeftDisj.gammaParent,d,ContractionBlock.extend_keep] using
        d.lowerL (Nat.le_refl 2) (BlockedSource.disjLLast f k)
    have hl := (G.lower_reindex_left e rfl p v).mpr hl0
    rw [BlockedLeftDisj.gammaParent_source] at hl
    have hi := G.lowerContraction_index_unique _ .left x (v.cast e) hx hl
    cases he : At.compare x (v.cast e) with
    | apart hn => exact False.elim (hn hi)
    | same =>
      have hcCast : PositionalCut.Clean h z (p.reindex e rfl) (v.cast e) := by
        simpa only [p,BlockedLeftDisj.gammaParent_source] using hc
      have hc0 := (PositionalCut.clean_reindex rfl rfl e rfl h z p v).mp hcCast
      have hs := blockedL_gammaDisj_rank_step f k h z hc0 (by
        intro K L M N b w c t hr hc'
        apply ih b w c t ?_ hc'
        have heq : PositionalCut.rank h z (p.reindex e rfl) (v.cast e) = PositionalCut.rank h z p v :=
          PositionalCut.rank_reindex rfl rfl e rfl h z p v
        rw [BlockedLeftDisj.gammaParent_source] at heq
        rw [heq]
        exact hr)
      have hsCast := (PositionalCut.eliminated_reindex rfl rfl e rfl h z p v).mpr hs
      change PositionalCut.Eliminated h z (p.reindex e rfl) (v.cast e) at hsCast
      rw [BlockedLeftDisj.gammaParent_source] at hsCast
      exact hsCast

end DosenPetric.Reduced.Gentzen.CutCommutation
