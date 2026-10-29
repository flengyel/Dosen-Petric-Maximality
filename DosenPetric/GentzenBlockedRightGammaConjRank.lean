module

public import DosenPetric.GentzenBlockedRightGammaConj

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BlockedRightConj

theorem gamma_first_descent {A B C : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++C::Y))) (g : G P Θ (B::(Z++C::T))) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (gammaParent f g)
      (At.there (B:=.conj A B) (BlockedMix.gammaBlock C Z T X Y).keep) h z) :
    PositionalCut.Clean f (At.there (B:=A) (BlockedMix.firstTag C X Y)) h z ∧
      PositionalCut.rank f (At.there (B:=A) (BlockedMix.firstTag C X Y)) h z <
        PositionalCut.rank (gammaParent f g)
          (At.there (B:=.conj A B) (BlockedMix.gammaBlock C Z T X Y).keep) h z := by
  have hv : (gammaBlock A B C X Y Z T).route.get
      (At.there (B:=.conj A B) ((BlockedMix.firstTag C X Y).before (Z++C::T))) =
      (gammaBlock A B C X Y Z T).keep := by
    rw [gammaBlock_route,Route.head_there,gammaBlock_keep]
    apply congrArg At.there
    simpa only [Route.firstBlock_get] using BlockedMix.gamma_second C Z T X Y
  have hd := (gammaBlock A B C X Y Z T).right_cut_descent (Nat.le_refl 2) (G.conjR f g)
    (At.there (B:=.conj A B) ((BlockedMix.firstTag C X Y).before (Z++C::T))) h z hv
    (by simpa only [gammaBlock_keep,gammaParent] using hc)
  have he := PositionalCut.conjR_left_first_descent f g (BlockedMix.firstTag C X Y) h z hd.1
  exact ⟨he.1,Nat.lt_trans he.2 (by simpa only [gammaBlock_keep,gammaParent] using hd.2)⟩

theorem gamma_second_descent {A B C : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++C::Y))) (g : G P Θ (B::(Z++C::T))) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (gammaParent f g)
      (At.there (B:=.conj A B) (BlockedMix.gammaBlock C Z T X Y).keep) h z) :
    PositionalCut.Clean g (At.there (B:=B) (BlockedMix.firstTag C Z T)) h z ∧
      PositionalCut.rank g (At.there (B:=B) (BlockedMix.firstTag C Z T)) h z <
        PositionalCut.rank (gammaParent f g)
          (At.there (B:=.conj A B) (BlockedMix.gammaBlock C Z T X Y).keep) h z := by
  have hv : (gammaBlock A B C X Y Z T).route.get
      (At.there (B:=.conj A B) (At.shift (X++C::Y) (BlockedMix.firstTag C Z T))) =
      (gammaBlock A B C X Y Z T).keep := by
    rw [gammaBlock_route,Route.head_there,gammaBlock_keep]
    apply congrArg At.there
    simpa only [Route.secondBlock_get] using BlockedMix.gamma_first C Z T X Y
  have hd := (gammaBlock A B C X Y Z T).right_cut_descent (Nat.le_refl 2) (G.conjR f g)
    (At.there (B:=.conj A B) (At.shift (X++C::Y) (BlockedMix.firstTag C Z T))) h z hv
    (by simpa only [gammaBlock_keep,gammaParent] using hc)
  have he := PositionalCut.conjR_left_second_descent f g (BlockedMix.firstTag C Z T) h z hd.1
  exact ⟨he.1,Nat.lt_trans he.2 (by simpa only [gammaBlock_keep,gammaParent] using hd.2)⟩

end BlockedRightConj
namespace CutCommutation

theorem blockedR_gammaConj_eliminated {A B C : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++C::Y))) (g : G P Θ (B::(Z++C::T))) (h : G P I J) (z : At I C)
    (hf : PositionalCut.Eliminated f (At.there (B:=A) (BlockedMix.firstTag C X Y)) h z)
    (hg : PositionalCut.Eliminated g (At.there (B:=B) (BlockedMix.firstTag C Z T)) h z) :
    PositionalCut.Eliminated (BlockedRightConj.gammaParent f g)
      (At.there (B:=.conj A B) (BlockedMix.gammaBlock C Z T X Y).keep) h z := by
  obtain ⟨k,hk,_,ek⟩ := hf
  obtain ⟨l,hl,_,el⟩ := hg
  let t := BlockedRightConj.parallel (BlockedMix.gammaSecondRoute C Z T X Y)
    (BlockedMix.gammaFirstRoute C Z T X Y) k l
  have ht : t.CutFree := by
    change t.cutCount = 0
    rw [BlockedRightConj.parallel_count]
    exact Nat.add_eq_zero_iff.mpr ⟨hk,hl⟩
  refine ⟨G.atomize t,G.atomize_cutFree t ht,G.atomize_atomized t,?_⟩
  exact (G.atomize_denote t).trans
    ((BlockedRightConj.parallel_congr _ _ _ _ _ _ ek el).trans (BlockedRightConj.gamma_equation f g h z).symm)

theorem blockedR_gammaConj_rank_step {A B C : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++C::Y))) (g : G P Θ (B::(Z++C::T))) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (BlockedRightConj.gammaParent f g)
      (At.there (B:=.conj A B) (BlockedMix.gammaBlock C Z T X Y).keep) h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank (BlockedRightConj.gammaParent f g)
        (At.there (B:=.conj A B) (BlockedMix.gammaBlock C Z T X Y).keep) h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (BlockedRightConj.gammaParent f g)
      (At.there (B:=.conj A B) (BlockedMix.gammaBlock C Z T X Y).keep) h z := by
  have hf := BlockedRightConj.gamma_first_descent f g h z hc
  have hg := BlockedRightConj.gamma_second_descent f g h z hc
  exact blockedR_gammaConj_eliminated f g h z
    (ih f (At.there (B:=A) (BlockedMix.firstTag C X Y)) h z hf.2 hf.1)
    (ih g (At.there (B:=B) (BlockedMix.firstTag C Z T)) h z hg.2 hg.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
