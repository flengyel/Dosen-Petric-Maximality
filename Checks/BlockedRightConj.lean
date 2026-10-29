module

import DosenPetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
namespace BlockedRightConjChecks

section
open BlockedRightConj
example {P : Type u} {A B C : NormalForm P} {Γ Θ X Y Z T : List (NormalForm P)}
    (f : G P Γ (A::(X++C::Y))) (g : G P Θ (B::(Z++C::T))) :
    gammaParent f g = BlockedSource.right2 C (Γ++Θ) (.conj A B::X) (Y++Z) T
      ((G.conjR f g).reindex rfl (by simp only [List.append_assoc,List.cons_append])) :=
  BlockedRightConj.gammaParent_source f g
end

section
open BlockedRightConj
example {P : Type u} {A B C : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++C::Y))) (g : G P Θ (B::(Z++C::T))) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (gammaParent f g)
      (At.there (B:=.conj A B) (BlockedMix.gammaBlock C Z T X Y).keep) h z).denote =
      ofTerm (parallel (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y)
        (PositionalCut.cut f (At.there (B:=A) (BlockedMix.firstTag C X Y)) h z)
        (PositionalCut.cut g (At.there (B:=B) (BlockedMix.firstTag C Z T)) h z)).denote :=
  BlockedRightConj.gamma_equation f g h z
end

section
open BlockedRightConj
example {P : Type u} {A B C : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++C::Y))) (g : G P Θ (B::(Z++C::T))) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (gammaParent f g)
      (At.there (B:=.conj A B) (BlockedMix.gammaBlock C Z T X Y).keep) h z) :
    PositionalCut.Clean f (At.there (B:=A) (BlockedMix.firstTag C X Y)) h z ∧
      PositionalCut.rank f (At.there (B:=A) (BlockedMix.firstTag C X Y)) h z <
        PositionalCut.rank (gammaParent f g)
          (At.there (B:=.conj A B) (BlockedMix.gammaBlock C Z T X Y).keep) h z :=
  BlockedRightConj.gamma_first_descent f g h z hc
end

section
open BlockedRightConj
example {P : Type u} {A B C : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++C::Y))) (g : G P Θ (B::(Z++C::T))) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (gammaParent f g)
      (At.there (B:=.conj A B) (BlockedMix.gammaBlock C Z T X Y).keep) h z) :
    PositionalCut.Clean g (At.there (B:=B) (BlockedMix.firstTag C Z T)) h z ∧
      PositionalCut.rank g (At.there (B:=B) (BlockedMix.firstTag C Z T)) h z <
        PositionalCut.rank (gammaParent f g)
          (At.there (B:=.conj A B) (BlockedMix.gammaBlock C Z T X Y).keep) h z :=
  BlockedRightConj.gamma_second_descent f g h z hc
end

section
open BlockedRightConj
example {P : Type u} {A B C : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++C::Y))) (g : G P Θ (B::(Z++C::T))) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (BlockedRightConj.gammaParent f g)
      (At.there (B:=.conj A B) (BlockedMix.gammaBlock C Z T X Y).keep) h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank (BlockedRightConj.gammaParent f g)
        (At.there (B:=.conj A B) (BlockedMix.gammaBlock C Z T X Y).keep) h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (BlockedRightConj.gammaParent f g)
      (At.there (B:=.conj A B) (BlockedMix.gammaBlock C Z T X Y).keep) h z :=
  CutCommutation.blockedR_gammaConj_rank_step f g h z hc ih
end

def literalChild (l : Literal Nat) : G Nat [.lit l] [.lit l,.lit l] :=
  G.thinR [.lit l] [.lit l] [] (.lit l) (G.identity l)

theorem literalChildCut (l : Literal Nat) : PositionalCut.Eliminated
    (literalChild l) (.there (.here (.lit l) [])) (G.identity l) (.here (.lit l) []) :=
  PositionalCut.thin_endomorphism (Γ:=[.lit l]) (Δ:=[.lit l]) (Λ:=[]) (.lit l)
    (G.identity l) (G.identity l) rfl True.intro True.intro

def constantChild : G Empty [] [.top,.top] := G.thinR [] [.top] [] .top G.topI

theorem constantChildCut : PositionalCut.Eliminated (P:=Empty)
    constantChild (.there (.here .top [])) G.topIdentity (.here .top []) :=
  PositionalCut.thin_thin [] [.top] [] [] [] [.top] .top G.topI G.topI rfl rfl True.intro True.intro

def twoTops : G Empty [.top] [.top,.top] := G.thinR [.top] [] [.top] .top G.topIdentity

def topPair : G Empty [.top,.top] [.top,.top] := G.thinL [] [.top] [.top,.top] .top twoTops

def threeTops : G Empty [.top,.top] [.top,.top,.top] :=
  G.thinR [.top,.top] [.top] [.top] .top topPair

def fourTops : G Empty [.top,.top] [.top,.top,.top,.top] :=
  G.thinR [.top,.top] [.top,.top] [.top] .top threeTops

theorem populatedChildCut : PositionalCut.Eliminated fourTops (.there (.there (.here .top [.top])))
    topPair (.here .top [.top]) :=
  PositionalCut.thin_thin [.top,.top] [.top,.top] [.top] [] [.top] [.top,.top] .top threeTops twoTops
    rfl rfl (by repeat constructor) (by repeat constructor)

example (l : Literal Nat) : PositionalCut.Eliminated
    (BlockedRightConj.gammaParent (X:=[]) (Y:=[]) (Z:=[]) (T:=[]) (literalChild l) (literalChild l))
    (At.there (B:=.conj (.lit l) (.lit l)) (BlockedMix.gammaBlock (.lit l) [] [] [] []).keep)
    (G.identity l) (.here (.lit l) []) :=
  CutCommutation.blockedR_gammaConj_eliminated (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
    (literalChild l) (literalChild l) (G.identity l) (.here (.lit l) []) (literalChildCut l) (literalChildCut l)

example : PositionalCut.Eliminated
    (BlockedRightConj.gammaParent (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
      (literalChild (.neg 0)) (literalChild (.neg 0)))
    (At.there (B:=.conj (.lit (.neg 0)) (.lit (.neg 0)))
      (BlockedMix.gammaBlock (.lit (.neg 0)) [] [] [] []).keep)
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) :=
  CutCommutation.blockedR_gammaConj_eliminated (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
    (literalChild (.neg 0)) (literalChild (.neg 0)) (G.identity (.neg 0)) (.here (.lit (.neg 0)) [])
    (literalChildCut (.neg 0)) (literalChildCut (.neg 0))

example : PositionalCut.Eliminated (P:=Empty)
    (BlockedRightConj.gammaParent (X:=[]) (Y:=[]) (Z:=[]) (T:=[]) constantChild constantChild)
    (At.there (B:=.conj .top .top) (BlockedMix.gammaBlock .top [] [] [] []).keep)
    G.topIdentity (.here .top []) :=
  CutCommutation.blockedR_gammaConj_eliminated (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
    constantChild constantChild G.topIdentity (.here .top []) constantChildCut constantChildCut

example : PositionalCut.Eliminated
    (BlockedRightConj.gammaParent (X:=[.top]) (Y:=[.top]) (Z:=[.top]) (T:=[.top]) fourTops fourTops)
    (At.there (B:=.conj .top .top) (BlockedMix.gammaBlock .top [.top] [.top] [.top] [.top]).keep)
    topPair (.here .top [.top]) :=
  CutCommutation.blockedR_gammaConj_eliminated (X:=[.top]) (Y:=[.top]) (Z:=[.top]) (T:=[.top])
    fourTops fourTops topPair (.here .top [.top]) populatedChildCut populatedChildCut

example :
    ((BlockedRightConj.gammaBlock (.top : NormalForm Empty) .top (.conj .top .top) [] [] [] []).route.get
      (.here (.conj .top .top) [.conj .top .top,.conj .top .top])).index = 0 := by rfl

end BlockedRightConjChecks

#print axioms DosenPetric.Reduced.Gentzen.ContractionSplice.head_right_binary

#print axioms DosenPetric.Reduced.Gentzen.DoubleConjSplice.equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedRightConj.canonical_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedRightConj.headParent_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedRightConj.gamma_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedRightConj.gamma_first_descent

#print axioms DosenPetric.Reduced.Gentzen.BlockedRightConj.gamma_second_descent

#print axioms DosenPetric.Reduced.Gentzen.CutCommutation.blockedR_gammaConj_rank_step
