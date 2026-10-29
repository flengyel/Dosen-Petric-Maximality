module

public import DosenPetric.GentzenBlockedRightMixSource
public import DosenPetric.GentzenBlockedGammaMix

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BlockedMix

def gammaRightParent {C : NormalForm P} {Γ Θ X Y Z T : List (NormalForm P)}
    (f : G P Γ (X++C::Y)) (g : G P Θ (Z++C::T)) :
    G P (Θ++Γ) (gaps [Z,T++X]++C::Y) :=
  (gammaBlock C X Y Z T).applyR (Nat.le_refl 2) (Θ++Γ) (G.mix f g)

theorem gammaRightParent_source {C : NormalForm P} {Γ Θ X Y Z T : List (NormalForm P)}
    (f : G P Γ (X++C::Y)) (g : G P Θ (Z++C::T)) :
    gammaRightParent f g = BlockedSource.right2 C (Θ++Γ) Z (T++X) Y
      ((G.mix f g).reindex rfl
        (by simp only [List.append_assoc,List.cons_append])) := by
  simp only [gammaRightParent,gammaBlock,ContractionBlock.applyR,BlockedSource.right2,G.reindex_trans]
  rfl

theorem rightParallel_congr {Y F H Γ Θ I J : List (NormalForm P)}
    (p : Route Y F) (q : Route Y H)
    (k k' : G P (I++Γ) (J++F)) (l l' : G P (I++Θ) (J++H))
    (hk : ofTerm k.denote = ofTerm k'.denote) (hl : ofTerm l.denote = ofTerm l'.denote) :
    ofTerm (rightParallel p q k l).denote = ofTerm (rightParallel p q k' l').denote := by
  unfold rightParallel
  rw [StructuralProgram.left_denote,StructuralProgram.left_denote,
    StructuralProgram.right_denote,StructuralProgram.right_denote]
  change comp _ (comp (ofTerm (Rules.mix k.denote l.denote)) _) = _
  rw [Rules.mix_congr hk hl]
  rfl

theorem gamma_right_equation {C : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (X++C::Y)) (g : G P Θ (Z++C::T)) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (gammaRightParent f g) (gammaBlock C X Y Z T).keep h z).denote =
      ofTerm (rightParallel (gammaFirstRoute C X Y Z T) (gammaSecondRoute C X Y Z T)
        (PositionalCut.cut f (firstTag C X Y) h z)
        (PositionalCut.cut g (firstTag C Z T) h z)).denote := by
  have he := right_source_denote (gammaBlock C X Y Z T).route (gammaBlock C X Y Z T).keep
    (firstTag C X Y) (firstTag C Z T) (gammaFirstRoute C X Y Z T) (gammaSecondRoute C X Y Z T)
    (gamma_first C X Y Z T) (gamma_second C X Y Z T)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm) f g
  have hp : ofTerm ((gammaBlock C X Y Z T).keep.toHead.right (gammaRightParent f g)).denote =
      ofTerm (rightHeadParent (gammaFirstRoute C X Y Z T) (gammaSecondRoute C X Y Z T)
        ((firstTag C X Y).toHead.right f) ((firstTag C Z T).toHead.right g)).denote := by
    rw [ExchangeScript.right_denote,gammaRightParent,ContractionBlock.denoteR,Laws.assoc]
    exact he
  apply (Rules.cut_congr hp (g := (z.toHead.left h).denote) rfl).trans
  exact rightHeadParent_equation (gammaFirstRoute C X Y Z T) (gammaSecondRoute C X Y Z T)
    ((firstTag C X Y).toHead.right f) ((firstTag C Z T).toHead.right g) (z.toHead.left h)

theorem gamma_right_first_descent {C : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (X++C::Y)) (g : G P Θ (Z++C::T)) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (gammaRightParent f g) (gammaBlock C X Y Z T).keep h z) :
    PositionalCut.Clean f (firstTag C X Y) h z ∧
      PositionalCut.rank f (firstTag C X Y) h z <
        PositionalCut.rank (gammaRightParent f g) (gammaBlock C X Y Z T).keep h z := by
  have hd := (gammaBlock C X Y Z T).right_cut_descent (Nat.le_refl 2) (G.mix f g)
    (At.shift (Z++C::T) (firstTag C X Y)) h z
    (by simpa only [Route.secondBlock_get] using gamma_first C X Y Z T) hc
  have he := PositionalCut.mix_left_first_descent f g (firstTag C X Y) h z hd.1
  exact ⟨he.1,Nat.lt_trans he.2 hd.2⟩

theorem gamma_right_second_descent {C : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (X++C::Y)) (g : G P Θ (Z++C::T)) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (gammaRightParent f g) (gammaBlock C X Y Z T).keep h z) :
    PositionalCut.Clean g (firstTag C Z T) h z ∧
      PositionalCut.rank g (firstTag C Z T) h z <
        PositionalCut.rank (gammaRightParent f g) (gammaBlock C X Y Z T).keep h z := by
  have hd := (gammaBlock C X Y Z T).right_cut_descent (Nat.le_refl 2) (G.mix f g)
    ((firstTag C Z T).before (X++C::Y)) h z
    (by simpa only [Route.firstBlock_get] using gamma_second C X Y Z T) hc
  have he := PositionalCut.mix_left_second_descent f g (firstTag C Z T) h z hd.1
  exact ⟨he.1,Nat.lt_trans he.2 hd.2⟩

end BlockedMix
namespace CutCommutation

theorem blockedR_gammaMix_eliminated {C : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (X++C::Y)) (g : G P Θ (Z++C::T)) (h : G P I J) (z : At I C)
    (hf : PositionalCut.Eliminated f (BlockedMix.firstTag C X Y) h z)
    (hg : PositionalCut.Eliminated g (BlockedMix.firstTag C Z T) h z) :
    PositionalCut.Eliminated (BlockedMix.gammaRightParent f g) (BlockedMix.gammaBlock C X Y Z T).keep h z := by
  obtain ⟨k,hk,_,ek⟩ := hf
  obtain ⟨l,hl,_,el⟩ := hg
  let t := BlockedMix.rightParallel (BlockedMix.gammaFirstRoute C X Y Z T)
    (BlockedMix.gammaSecondRoute C X Y Z T) k l
  have ht : t.CutFree := by
    change t.cutCount = 0
    rw [BlockedMix.rightParallel_count]
    exact Nat.add_eq_zero_iff.mpr ⟨hk,hl⟩
  refine ⟨G.atomize t,G.atomize_cutFree t ht,G.atomize_atomized t,?_⟩
  exact (G.atomize_denote t).trans
    ((BlockedMix.rightParallel_congr _ _ _ _ _ _ ek el).trans (BlockedMix.gamma_right_equation f g h z).symm)

theorem blockedR_gammaMix_rank_step {C : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (X++C::Y)) (g : G P Θ (Z++C::T)) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (BlockedMix.gammaRightParent f g) (BlockedMix.gammaBlock C X Y Z T).keep h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w <
        PositionalCut.rank (BlockedMix.gammaRightParent f g) (BlockedMix.gammaBlock C X Y Z T).keep h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (BlockedMix.gammaRightParent f g) (BlockedMix.gammaBlock C X Y Z T).keep h z := by
  have hf := BlockedMix.gamma_right_first_descent f g h z hc
  have hg := BlockedMix.gamma_right_second_descent f g h z hc
  exact blockedR_gammaMix_eliminated f g h z
    (ih f (BlockedMix.firstTag C X Y) h z hf.2 hf.1)
    (ih g (BlockedMix.firstTag C Z T) h z hg.2 hg.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
