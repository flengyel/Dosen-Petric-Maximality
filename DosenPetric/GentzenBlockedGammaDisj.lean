module

public import DosenPetric.GentzenBlockedDisjSource
public import DosenPetric.GentzenTerminalCutDescent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BlockedDisj

def gammaParent {A B C : NormalForm P} {F U X Y Z T : List (NormalForm P)}
    (f : G P (F++[A]) (X++C::Y)) (g : G P (U++[B]) (Z++C::T)) :
    G P ((F++U)++[.disj A B]) (gaps [X,Y++Z]++C::T) :=
  (BlockedMix.gammaBlock C Z T X Y).applyR (Nat.le_refl 2) _ (BlockedSource.disjLLast f g)

theorem gammaParent_source {A B C : NormalForm P} {F U X Y Z T : List (NormalForm P)}
    (f : G P (F++[A]) (X++C::Y)) (g : G P (U++[B]) (Z++C::T)) :
    gammaParent f g = BlockedSource.right2 C ((F++U)++[.disj A B]) X (Y++Z) T
      ((BlockedSource.disjLLast f g).reindex rfl
        (by simp only [List.append_assoc,List.cons_append])) := by
  simp only [gammaParent,BlockedMix.gammaBlock,ContractionBlock.applyR,BlockedSource.right2,G.reindex_trans]
  rfl

theorem parallel_congr {F U D E Y T J : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (k k' : G P (T++(F++[A])) (J++D)) (l l' : G P (T++(U++[B])) (J++E))
    (hk : ofTerm k.denote = ofTerm k'.denote) (hl : ofTerm l.denote = ofTerm l'.denote) :
    ofTerm (parallel p q k l).denote = ofTerm (parallel p q k' l').denote := by
  unfold parallel
  simp only [StructuralProgram.left_denote,StructuralProgram.right_denote,
    TerminalFold.disjLLast_denote,ExchangeScript.left_denote,hk,hl]

theorem gamma_equation {A B C : NormalForm P} {F U X Y Z T I J : List (NormalForm P)}
    (f : G P (F++[A]) (X++C::Y)) (g : G P (U++[B]) (Z++C::T)) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep h z).denote =
      ofTerm (parallel (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y)
        (PositionalCut.cut f (BlockedMix.firstTag C X Y) h z)
        (PositionalCut.cut g (BlockedMix.firstTag C Z T) h z)).denote := by
  have he := source_denote (BlockedMix.gammaBlock C Z T X Y).route (BlockedMix.gammaBlock C Z T X Y).keep
    (BlockedMix.firstTag C X Y) (BlockedMix.firstTag C Z T)
    (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y)
    (BlockedMix.gamma_second C Z T X Y) (BlockedMix.gamma_first C Z T X Y)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm) f g
  have hp : ofTerm ((BlockedMix.gammaBlock C Z T X Y).keep.toHead.right (gammaParent f g)).denote =
      ofTerm (headParent (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y)
        ((BlockedMix.firstTag C X Y).toHead.right f) ((BlockedMix.firstTag C Z T).toHead.right g)).denote := by
    rw [ExchangeScript.right_denote,gammaParent,ContractionBlock.denoteR,Laws.assoc]
    exact he
  apply (Rules.cut_congr hp (g := (z.toHead.left h).denote) rfl).trans
  exact headParent_equation (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y)
    ((BlockedMix.firstTag C X Y).toHead.right f) ((BlockedMix.firstTag C Z T).toHead.right g) (z.toHead.left h)

theorem gamma_first_descent {A B C : NormalForm P} {F U X Y Z T I J : List (NormalForm P)}
    (f : G P (F++[A]) (X++C::Y)) (g : G P (U++[B]) (Z++C::T)) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep h z) :
    PositionalCut.Clean f (BlockedMix.firstTag C X Y) h z ∧
      PositionalCut.rank f (BlockedMix.firstTag C X Y) h z <
        PositionalCut.rank (gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep h z := by
  have hd := (BlockedMix.gammaBlock C Z T X Y).right_cut_descent (Nat.le_refl 2)
    (BlockedSource.disjLLast f g) ((BlockedMix.firstTag C X Y).before (Z++C::T)) h z
    (by simpa only [Route.firstBlock_get] using BlockedMix.gamma_second C Z T X Y) hc
  have he := BlockedSource.disjLLast_left_first_descent f g (BlockedMix.firstTag C X Y) h z hd.1
  exact ⟨he.1,Nat.lt_trans he.2 hd.2⟩

theorem gamma_second_descent {A B C : NormalForm P} {F U X Y Z T I J : List (NormalForm P)}
    (f : G P (F++[A]) (X++C::Y)) (g : G P (U++[B]) (Z++C::T)) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep h z) :
    PositionalCut.Clean g (BlockedMix.firstTag C Z T) h z ∧
      PositionalCut.rank g (BlockedMix.firstTag C Z T) h z <
        PositionalCut.rank (gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep h z := by
  have hd := (BlockedMix.gammaBlock C Z T X Y).right_cut_descent (Nat.le_refl 2)
    (BlockedSource.disjLLast f g) (At.shift (X++C::Y) (BlockedMix.firstTag C Z T)) h z
    (by simpa only [Route.secondBlock_get] using BlockedMix.gamma_first C Z T X Y) hc
  have he := BlockedSource.disjLLast_left_second_descent f g (BlockedMix.firstTag C Z T) h z hd.1
  exact ⟨he.1,Nat.lt_trans he.2 hd.2⟩

end BlockedDisj
namespace CutCommutation

theorem blockedR_gammaDisj_eliminated {A B C : NormalForm P} {F U X Y Z T I J : List (NormalForm P)}
    (f : G P (F++[A]) (X++C::Y)) (g : G P (U++[B]) (Z++C::T)) (h : G P I J) (z : At I C)
    (hf : PositionalCut.Eliminated f (BlockedMix.firstTag C X Y) h z)
    (hg : PositionalCut.Eliminated g (BlockedMix.firstTag C Z T) h z) :
    PositionalCut.Eliminated (BlockedDisj.gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep h z := by
  obtain ⟨k,hk,_,ek⟩ := hf
  obtain ⟨l,hl,_,el⟩ := hg
  let t := BlockedDisj.parallel (BlockedMix.gammaSecondRoute C Z T X Y)
    (BlockedMix.gammaFirstRoute C Z T X Y) k l
  have ht : t.CutFree := by
    change t.cutCount = 0
    rw [BlockedDisj.parallel_count]
    exact Nat.add_eq_zero_iff.mpr ⟨hk,hl⟩
  refine ⟨G.atomize t,G.atomize_cutFree t ht,G.atomize_atomized t,?_⟩
  exact (G.atomize_denote t).trans
    ((BlockedDisj.parallel_congr _ _ _ _ _ _ ek el).trans (BlockedDisj.gamma_equation f g h z).symm)

theorem blockedR_gammaDisj_rank_step {A B C : NormalForm P} {F U X Y Z T I J : List (NormalForm P)}
    (f : G P (F++[A]) (X++C::Y)) (g : G P (U++[B]) (Z++C::T)) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (BlockedDisj.gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w <
        PositionalCut.rank (BlockedDisj.gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (BlockedDisj.gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep h z := by
  have hf := BlockedDisj.gamma_first_descent f g h z hc
  have hg := BlockedDisj.gamma_second_descent f g h z hc
  exact blockedR_gammaDisj_eliminated f g h z
    (ih f (BlockedMix.firstTag C X Y) h z hf.2 hf.1)
    (ih g (BlockedMix.firstTag C Z T) h z hg.2 hg.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
