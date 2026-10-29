module

public import DosenPetric.GentzenBlockedGammaMixData
public import DosenPetric.GentzenSelectedContractionDescent
public import DosenPetric.GentzenBinaryMixLeftStep

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BlockedMix

theorem parallel_congr {Y F H D E I R : List (NormalForm P)}
    (p : Route Y F) (q : Route Y H)
    (k k' : G P (F++I) (D++R)) (l l' : G P (H++I) (E++R))
    (hk : ofTerm k.denote = ofTerm k'.denote) (hl : ofTerm l.denote = ofTerm l'.denote) :
    ofTerm (parallel p q k l).denote = ofTerm (parallel p q k' l').denote := by
  unfold parallel
  rw [StructuralProgram.left_denote,StructuralProgram.left_denote,
    StructuralProgram.right_denote,StructuralProgram.right_denote]
  change comp _ (comp (ofTerm (Rules.mix k.denote l.denote)) _) = _
  rw [Rules.mix_congr hk hl]
  rfl

theorem gamma_equation {C : NormalForm P} {X Y Z T Δ Λ I J : List (NormalForm P)}
    (f : G P (X++C::Y) Δ) (g : G P (Z++C::T) Λ) (h : G P I J) (z : At J C) :
    ofTerm (PositionalCut.cut h z (gammaParent f g) (gammaBlock C X Y Z T).keep).denote =
      ofTerm (parallel (gammaFirstRoute C X Y Z T) (gammaSecondRoute C X Y Z T)
        (PositionalCut.cut h z f (firstTag C X Y))
        (PositionalCut.cut h z g (firstTag C Z T))).denote := by
  have he := source_denote (gammaBlock C X Y Z T).route (gammaBlock C X Y Z T).keep
    (firstTag C X Y) (firstTag C Z T) (gammaFirstRoute C X Y Z T) (gammaSecondRoute C X Y Z T)
    (gamma_first C X Y Z T) (gamma_second C X Y Z T)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm) f g
  have hp : ofTerm ((gammaBlock C X Y Z T).keep.toHead.left (gammaParent f g)).denote =
      ofTerm (headParent (gammaFirstRoute C X Y Z T) (gammaSecondRoute C X Y Z T)
        ((firstTag C X Y).toHead.left f) ((firstTag C Z T).toHead.left g)).denote := by
    rw [ExchangeScript.left_denote,gammaParent,ContractionBlock.denoteL]
    exact he
  apply (Rules.cut_congr (f := (z.toHead.right h).denote) rfl hp).trans
  exact headParent_equation (gammaFirstRoute C X Y Z T) (gammaSecondRoute C X Y Z T)
    ((firstTag C X Y).toHead.left f) ((firstTag C Z T).toHead.left g) (z.toHead.right h)

theorem gamma_first_descent {C : NormalForm P} {X Y Z T Δ Λ I J : List (NormalForm P)}
    (f : G P (X++C::Y) Δ) (g : G P (Z++C::T) Λ) (h : G P I J) (z : At J C)
    (hc : PositionalCut.Clean h z (gammaParent f g) (gammaBlock C X Y Z T).keep) :
    PositionalCut.Clean h z f (firstTag C X Y) ∧
      PositionalCut.rank h z f (firstTag C X Y) <
        PositionalCut.rank h z (gammaParent f g) (gammaBlock C X Y Z T).keep := by
  have hd := (gammaBlock C X Y Z T).left_cut_descent (Nat.le_refl 2) (G.mix f g)
    (At.shift (Z++C::T) (firstTag C X Y)) h z (by simpa only [Route.secondBlock_get] using gamma_first C X Y Z T) hc
  have he := PositionalCut.mix_right_first_descent f g h z (firstTag C X Y) hd.1
  exact ⟨he.1,Nat.lt_trans he.2 hd.2⟩

theorem gamma_second_descent {C : NormalForm P} {X Y Z T Δ Λ I J : List (NormalForm P)}
    (f : G P (X++C::Y) Δ) (g : G P (Z++C::T) Λ) (h : G P I J) (z : At J C)
    (hc : PositionalCut.Clean h z (gammaParent f g) (gammaBlock C X Y Z T).keep) :
    PositionalCut.Clean h z g (firstTag C Z T) ∧
      PositionalCut.rank h z g (firstTag C Z T) <
        PositionalCut.rank h z (gammaParent f g) (gammaBlock C X Y Z T).keep := by
  have hd := (gammaBlock C X Y Z T).left_cut_descent (Nat.le_refl 2) (G.mix f g)
    ((firstTag C Z T).before (X++C::Y)) h z (by simpa only [Route.firstBlock_get] using gamma_second C X Y Z T) hc
  have he := PositionalCut.mix_right_second_descent f g h z (firstTag C Z T) hd.1
  exact ⟨he.1,Nat.lt_trans he.2 hd.2⟩

end BlockedMix
namespace CutCommutation

theorem blockedL_gammaMix_eliminated {C : NormalForm P} {X Y Z T Δ Λ I J : List (NormalForm P)}
    (f : G P (X++C::Y) Δ) (g : G P (Z++C::T) Λ) (h : G P I J) (z : At J C)
    (hf : PositionalCut.Eliminated h z f (BlockedMix.firstTag C X Y))
    (hg : PositionalCut.Eliminated h z g (BlockedMix.firstTag C Z T)) :
    PositionalCut.Eliminated h z (BlockedMix.gammaParent f g) (BlockedMix.gammaBlock C X Y Z T).keep := by
  obtain ⟨k,hk,_,ek⟩ := hf
  obtain ⟨l,hl,_,el⟩ := hg
  let t := BlockedMix.parallel (BlockedMix.gammaFirstRoute C X Y Z T)
    (BlockedMix.gammaSecondRoute C X Y Z T) k l
  have ht : t.CutFree := by
    change t.cutCount = 0
    rw [BlockedMix.parallel_count]
    exact Nat.add_eq_zero_iff.mpr ⟨hk,hl⟩
  refine ⟨G.atomize t,G.atomize_cutFree t ht,G.atomize_atomized t,?_⟩
  exact (G.atomize_denote t).trans
    ((BlockedMix.parallel_congr _ _ _ _ _ _ ek el).trans (BlockedMix.gamma_equation f g h z).symm)

theorem blockedL_gammaMix_rank_step {C : NormalForm P} {X Y Z T Δ Λ I J : List (NormalForm P)}
    (f : G P (X++C::Y) Δ) (g : G P (Z++C::T) Λ) (h : G P I J) (z : At J C)
    (hc : PositionalCut.Clean h z (BlockedMix.gammaParent f g) (BlockedMix.gammaBlock C X Y Z T).keep)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w <
        PositionalCut.rank h z (BlockedMix.gammaParent f g) (BlockedMix.gammaBlock C X Y Z T).keep →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (BlockedMix.gammaParent f g) (BlockedMix.gammaBlock C X Y Z T).keep := by
  have hf := BlockedMix.gamma_first_descent f g h z hc
  have hg := BlockedMix.gamma_second_descent f g h z hc
  exact blockedL_gammaMix_eliminated f g h z
    (ih h z f (BlockedMix.firstTag C X Y) hf.2 hf.1)
    (ih h z g (BlockedMix.firstTag C Z T) hg.2 hg.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
