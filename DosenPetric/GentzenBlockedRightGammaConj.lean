module

public import DosenPetric.GentzenBlockedRightConjBlock

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedRightConj
universe u
variable {P : Type u}

def gammaParent {A B C : NormalForm P} {Γ Θ X Y Z T : List (NormalForm P)}
    (f : G P Γ (A::(X++C::Y))) (g : G P Θ (B::(Z++C::T))) :
    G P (Γ++Θ) (.conj A B::(gaps [X,Y++Z]++C::T)) :=
  (gammaBlock A B C X Y Z T).applyR (Nat.le_refl 2) _ (G.conjR f g)

theorem gammaParent_source {A B C : NormalForm P} {Γ Θ X Y Z T : List (NormalForm P)}
    (f : G P Γ (A::(X++C::Y))) (g : G P Θ (B::(Z++C::T))) :
    gammaParent f g = BlockedSource.right2 C (Γ++Θ) (.conj A B::X) (Y++Z) T
      ((G.conjR f g).reindex rfl (by simp only [List.append_assoc,List.cons_append])) := by
  simp only [gammaParent,gammaBlock,ContractionBlock.applyR,BlockedSource.right2,G.reindex_trans]
  rfl

theorem gamma_equation {A B C : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++C::Y))) (g : G P Θ (B::(Z++C::T))) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (gammaParent f g)
      (At.there (B:=.conj A B) (BlockedMix.gammaBlock C Z T X Y).keep) h z).denote =
      ofTerm (parallel (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y)
        (PositionalCut.cut f (At.there (B:=A) (BlockedMix.firstTag C X Y)) h z)
        (PositionalCut.cut g (At.there (B:=B) (BlockedMix.firstTag C Z T)) h z)).denote := by
  have he := source_denote (BlockedMix.gammaBlock C Z T X Y).route (BlockedMix.gammaBlock C Z T X Y).keep
    (BlockedMix.firstTag C X Y) (BlockedMix.firstTag C Z T)
    (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y)
    (BlockedMix.gamma_second C Z T X Y) (BlockedMix.gamma_first C Z T X Y)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm) f g
  have hp : ofTerm ((At.there (B:=.conj A B) (BlockedMix.gammaBlock C Z T X Y).keep).toHead.right
      (gammaParent f g)).denote =
      ofTerm (headParent (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y)
        (((BlockedMix.firstTag C X Y).toHead.consFixed A).right f)
        (((BlockedMix.firstTag C Z T).toHead.consFixed B).right g)).denote := by
    rw [ExchangeScript.right_denote,gammaParent,ContractionBlock.denoteR,gammaBlock_route]
    exact he
  apply (Rules.cut_congr hp rfl).trans
  apply (headParent_equation (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y)
    (((BlockedMix.firstTag C X Y).toHead.consFixed A).right f)
    (((BlockedMix.firstTag C Z T).toHead.consFixed B).right g) (z.toHead.left h)).trans
  apply parallel_congr
  · exact (BinaryLogical.leftFirstChild_factor f (BlockedMix.firstTag C X Y) h z).symm
  · exact (BinaryLogical.leftFirstChild_factor g (BlockedMix.firstTag C Z T) h z).symm

end DosenPetric.Reduced.Gentzen.BlockedRightConj
