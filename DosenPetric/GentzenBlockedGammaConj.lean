module

public import DosenPetric.GentzenBlockedConjEquation
public import DosenPetric.GentzenBlockedGammaMix

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BlockedConj

def gammaParent {A B C : NormalForm P} {X Y Z T Δ Λ : List (NormalForm P)}
    (f : G P (X++C::Y) (A::Δ)) (g : G P (Z++C::T) (B::Λ)) :
    G P (gaps [X,Y++Z]++C::T) (.conj A B::(Δ++Λ)) :=
  (BlockedMix.gammaBlock C Z T X Y).applyL (Nat.le_refl 2) _ (G.conjR f g)

theorem gammaParent_source {A B C : NormalForm P} {X Y Z T Δ Λ : List (NormalForm P)}
    (f : G P (X++C::Y) (A::Δ)) (g : G P (Z++C::T) (B::Λ)) :
    gammaParent f g = BlockedSource.left2 C X (Y++Z) T (.conj A B::(Δ++Λ))
      ((G.conjR f g).reindex (by simp only [List.append_assoc,List.cons_append]) rfl) := by
  simp only [gammaParent,BlockedMix.gammaBlock,ContractionBlock.applyL,BlockedSource.left2,G.reindex_trans]
  rfl

theorem parallel_congr {Y F H D E I R : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y F) (q : Route Y H)
    (k k' : G P (F++I) (A::(D++R))) (l l' : G P (H++I) (B::(E++R)))
    (hk : ofTerm k.denote = ofTerm k'.denote) (hl : ofTerm l.denote = ofTerm l'.denote) :
    ofTerm (parallel p q k l).denote = ofTerm (parallel p q k' l').denote := by
  unfold parallel
  rw [StructuralProgram.left_denote,StructuralProgram.left_denote,
    StructuralProgram.right_denote,StructuralProgram.right_denote]
  change comp _ (comp (ofTerm (Rules.conjRight k.denote l.denote)) _) = _
  rw [Rules.conjRight_congr hk hl]
  rfl

theorem gamma_equation {A B C : NormalForm P} {X Y Z T Δ Λ I J : List (NormalForm P)}
    (f : G P (X++C::Y) (A::Δ)) (g : G P (Z++C::T) (B::Λ)) (h : G P I J) (z : At J C) :
    ofTerm (PositionalCut.cut h z (gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep).denote =
      ofTerm (parallel (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y)
        (PositionalCut.cut h z f (BlockedMix.firstTag C X Y))
        (PositionalCut.cut h z g (BlockedMix.firstTag C Z T))).denote := by
  have he := source_denote (BlockedMix.gammaBlock C Z T X Y).route (BlockedMix.gammaBlock C Z T X Y).keep
    (BlockedMix.firstTag C X Y) (BlockedMix.firstTag C Z T)
    (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y)
    (BlockedMix.gamma_second C Z T X Y) (BlockedMix.gamma_first C Z T X Y)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm) f g
  have hp : ofTerm ((BlockedMix.gammaBlock C Z T X Y).keep.toHead.left (gammaParent f g)).denote =
      ofTerm (headParent (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y)
        ((BlockedMix.firstTag C X Y).toHead.left f) ((BlockedMix.firstTag C Z T).toHead.left g)).denote := by
    rw [ExchangeScript.left_denote,gammaParent,ContractionBlock.denoteL]
    exact he
  apply (Rules.cut_congr (f := (z.toHead.right h).denote) rfl hp).trans
  exact headParent_equation (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y)
    ((BlockedMix.firstTag C X Y).toHead.left f) ((BlockedMix.firstTag C Z T).toHead.left g) (z.toHead.right h)

theorem gamma_first_descent {A B C : NormalForm P} {X Y Z T Δ Λ I J : List (NormalForm P)}
    (f : G P (X++C::Y) (A::Δ)) (g : G P (Z++C::T) (B::Λ)) (h : G P I J) (z : At J C)
    (hc : PositionalCut.Clean h z (gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep) :
    PositionalCut.Clean h z f (BlockedMix.firstTag C X Y) ∧
      PositionalCut.rank h z f (BlockedMix.firstTag C X Y) <
        PositionalCut.rank h z (gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep := by
  have hd := (BlockedMix.gammaBlock C Z T X Y).left_cut_descent (Nat.le_refl 2) (G.conjR f g)
    ((BlockedMix.firstTag C X Y).before (Z++C::T)) h z
    (by simpa only [Route.firstBlock_get] using BlockedMix.gamma_second C Z T X Y) hc
  have he := PositionalCut.conjR_right_first_descent f g h z (BlockedMix.firstTag C X Y) hd.1
  exact ⟨he.1,Nat.lt_trans he.2 hd.2⟩

theorem gamma_second_descent {A B C : NormalForm P} {X Y Z T Δ Λ I J : List (NormalForm P)}
    (f : G P (X++C::Y) (A::Δ)) (g : G P (Z++C::T) (B::Λ)) (h : G P I J) (z : At J C)
    (hc : PositionalCut.Clean h z (gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep) :
    PositionalCut.Clean h z g (BlockedMix.firstTag C Z T) ∧
      PositionalCut.rank h z g (BlockedMix.firstTag C Z T) <
        PositionalCut.rank h z (gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep := by
  have hd := (BlockedMix.gammaBlock C Z T X Y).left_cut_descent (Nat.le_refl 2) (G.conjR f g)
    (At.shift (X++C::Y) (BlockedMix.firstTag C Z T)) h z
    (by simpa only [Route.secondBlock_get] using BlockedMix.gamma_first C Z T X Y) hc
  have he := PositionalCut.conjR_right_second_descent f g h z (BlockedMix.firstTag C Z T) hd.1
  exact ⟨he.1,Nat.lt_trans he.2 hd.2⟩

end BlockedConj
namespace CutCommutation

theorem blockedL_gammaConj_eliminated {A B C : NormalForm P} {X Y Z T Δ Λ I J : List (NormalForm P)}
    (f : G P (X++C::Y) (A::Δ)) (g : G P (Z++C::T) (B::Λ)) (h : G P I J) (z : At J C)
    (hf : PositionalCut.Eliminated h z f (BlockedMix.firstTag C X Y))
    (hg : PositionalCut.Eliminated h z g (BlockedMix.firstTag C Z T)) :
    PositionalCut.Eliminated h z (BlockedConj.gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep := by
  obtain ⟨k,hk,_,ek⟩ := hf
  obtain ⟨l,hl,_,el⟩ := hg
  let t := BlockedConj.parallel (BlockedMix.gammaSecondRoute C Z T X Y)
    (BlockedMix.gammaFirstRoute C Z T X Y) k l
  have ht : t.CutFree := by
    change t.cutCount = 0
    rw [BlockedConj.parallel_count]
    exact Nat.add_eq_zero_iff.mpr ⟨hk,hl⟩
  refine ⟨G.atomize t,G.atomize_cutFree t ht,G.atomize_atomized t,?_⟩
  exact (G.atomize_denote t).trans
    ((BlockedConj.parallel_congr _ _ _ _ _ _ ek el).trans (BlockedConj.gamma_equation f g h z).symm)

theorem blockedL_gammaConj_rank_step {A B C : NormalForm P} {X Y Z T Δ Λ I J : List (NormalForm P)}
    (f : G P (X++C::Y) (A::Δ)) (g : G P (Z++C::T) (B::Λ)) (h : G P I J) (z : At J C)
    (hc : PositionalCut.Clean h z (BlockedConj.gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w <
        PositionalCut.rank h z (BlockedConj.gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (BlockedConj.gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep := by
  have hf := BlockedConj.gamma_first_descent f g h z hc
  have hg := BlockedConj.gamma_second_descent f g h z hc
  exact blockedL_gammaConj_eliminated f g h z
    (ih h z f (BlockedMix.firstTag C X Y) hf.2 hf.1)
    (ih h z g (BlockedMix.firstTag C Z T) hg.2 hg.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
