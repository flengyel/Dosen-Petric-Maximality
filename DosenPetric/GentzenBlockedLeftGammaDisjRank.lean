module

public import DosenPetric.GentzenBlockedLeftGammaDisj
public import DosenPetric.GentzenTerminalInputCutDescent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BlockedLeftDisj

theorem gamma_first_descent {A B C : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++C::Y)++[A]) D) (g : G P ((Z++C::T)++[B]) E) (h : G P I J) (z : At J C)
    (hc : PositionalCut.Clean h z (gammaParent f g)
      ((BlockedMix.gammaBlock C Z T X Y).keep.before [.disj A B])) :
    PositionalCut.Clean h z f ((BlockedMix.firstTag C X Y).before [A]) ∧
      PositionalCut.rank h z f ((BlockedMix.firstTag C X Y).before [A]) <
        PositionalCut.rank h z (gammaParent f g)
          ((BlockedMix.gammaBlock C Z T X Y).keep.before [.disj A B]) := by
  have hv : (BlockedMix.gammaBlock C Z T X Y).route.get
      ((BlockedMix.firstTag C X Y).before (Z++C::T)) = (BlockedMix.gammaBlock C Z T X Y).keep := by
    simpa only [Route.firstBlock_get] using BlockedMix.gamma_second C Z T X Y
  have hd := ((BlockedMix.gammaBlock C Z T X Y).extend [.disj A B]).left_cut_descent
    (Nat.le_refl 2) (BlockedSource.disjLLast f g)
    (((BlockedMix.firstTag C X Y).before (Z++C::T)).before [.disj A B]) h z
    (by rw [ContractionBlock.extend_before,hv,ContractionBlock.extend_keep])
    (by simpa only [ContractionBlock.extend_keep,gammaParent] using hc)
  have he := BlockedSource.disjLLast_right_first_descent f g (BlockedMix.firstTag C X Y) h z hd.1
  exact ⟨he.1,Nat.lt_trans he.2 (by simpa only [ContractionBlock.extend_keep,gammaParent] using hd.2)⟩

theorem gamma_second_descent {A B C : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++C::Y)++[A]) D) (g : G P ((Z++C::T)++[B]) E) (h : G P I J) (z : At J C)
    (hc : PositionalCut.Clean h z (gammaParent f g)
      ((BlockedMix.gammaBlock C Z T X Y).keep.before [.disj A B])) :
    PositionalCut.Clean h z g ((BlockedMix.firstTag C Z T).before [B]) ∧
      PositionalCut.rank h z g ((BlockedMix.firstTag C Z T).before [B]) <
        PositionalCut.rank h z (gammaParent f g)
          ((BlockedMix.gammaBlock C Z T X Y).keep.before [.disj A B]) := by
  have hv : (BlockedMix.gammaBlock C Z T X Y).route.get
      (At.shift (X++C::Y) (BlockedMix.firstTag C Z T)) = (BlockedMix.gammaBlock C Z T X Y).keep := by
    simpa only [Route.secondBlock_get] using BlockedMix.gamma_first C Z T X Y
  have hd := ((BlockedMix.gammaBlock C Z T X Y).extend [.disj A B]).left_cut_descent
    (Nat.le_refl 2) (BlockedSource.disjLLast f g)
    ((At.shift (X++C::Y) (BlockedMix.firstTag C Z T)).before [.disj A B]) h z
    (by rw [ContractionBlock.extend_before,hv,ContractionBlock.extend_keep])
    (by simpa only [ContractionBlock.extend_keep,gammaParent] using hc)
  have he := BlockedSource.disjLLast_right_second_descent f g (BlockedMix.firstTag C Z T) h z hd.1
  exact ⟨he.1,Nat.lt_trans he.2 (by simpa only [ContractionBlock.extend_keep,gammaParent] using hd.2)⟩

end BlockedLeftDisj
namespace CutCommutation

theorem blockedL_gammaDisj_eliminated {A B C : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++C::Y)++[A]) D) (g : G P ((Z++C::T)++[B]) E) (h : G P I J) (z : At J C)
    (hf : PositionalCut.Eliminated h z f ((BlockedMix.firstTag C X Y).before [A]))
    (hg : PositionalCut.Eliminated h z g ((BlockedMix.firstTag C Z T).before [B])) :
    PositionalCut.Eliminated h z (BlockedLeftDisj.gammaParent f g)
      ((BlockedMix.gammaBlock C Z T X Y).keep.before [.disj A B]) := by
  obtain ⟨k,hk,_,ek⟩ := hf
  obtain ⟨l,hl,_,el⟩ := hg
  let t := BlockedLeftDisj.selectedParallel (BlockedMix.gammaBlock C Z T X Y).keep
    (BlockedMix.firstTag C X Y) (BlockedMix.firstTag C Z T)
    (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y) k l
  have ht : t.CutFree := by
    change t.cutCount = 0
    rw [BlockedLeftDisj.selectedParallel_count]
    exact Nat.add_eq_zero_iff.mpr ⟨hk,hl⟩
  refine ⟨G.atomize t,G.atomize_cutFree t ht,G.atomize_atomized t,?_⟩
  exact (G.atomize_denote t).trans
    ((BlockedLeftDisj.selectedParallel_congr _ _ _ _ _ _ _ _ _ ek el).trans
      (BlockedLeftDisj.gamma_equation f g h z).symm)

theorem blockedL_gammaDisj_rank_step {A B C : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++C::Y)++[A]) D) (g : G P ((Z++C::T)++[B]) E) (h : G P I J) (z : At J C)
    (hc : PositionalCut.Clean h z (BlockedLeftDisj.gammaParent f g)
      ((BlockedMix.gammaBlock C Z T X Y).keep.before [.disj A B]))
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank h z (BlockedLeftDisj.gammaParent f g)
        ((BlockedMix.gammaBlock C Z T X Y).keep.before [.disj A B]) →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (BlockedLeftDisj.gammaParent f g)
      ((BlockedMix.gammaBlock C Z T X Y).keep.before [.disj A B]) := by
  have hf := BlockedLeftDisj.gamma_first_descent f g h z hc
  have hg := BlockedLeftDisj.gamma_second_descent f g h z hc
  exact blockedL_gammaDisj_eliminated f g h z
    (ih h z f ((BlockedMix.firstTag C X Y).before [A]) hf.2 hf.1)
    (ih h z g ((BlockedMix.firstTag C Z T).before [B]) hg.2 hg.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
