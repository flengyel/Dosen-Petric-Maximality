module

import DosenPetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
namespace BlockedLeftDisjChecks

section
open BlockedLeftDisj
example {P : Type u} {A B C : NormalForm P} {X Y Z T D E : List (NormalForm P)}
    (f : G P ((X++C::Y)++[A]) D) (g : G P ((Z++C::T)++[B]) E) :
    (gammaParent f g).reindex (by simp only [List.append_assoc,List.cons_append]) rfl =
      BlockedSource.left2 C X (Y++Z) (T++[.disj A B]) (D++E)
        ((BlockedSource.disjLLast f g).reindex
          (by simp only [List.append_assoc,List.cons_append]) rfl) :=
  BlockedLeftDisj.gammaParent_source f g
end

section
open BlockedLeftDisj
example {P : Type u} {A B C : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++C::Y)++[A]) D) (g : G P ((Z++C::T)++[B]) E) (h : G P I J) (z : At J C)
    (hc : PositionalCut.Clean h z (gammaParent f g)
      ((BlockedMix.gammaBlock C Z T X Y).keep.before [.disj A B])) :
    PositionalCut.Clean h z f ((BlockedMix.firstTag C X Y).before [A]) ∧
      PositionalCut.rank h z f ((BlockedMix.firstTag C X Y).before [A]) <
        PositionalCut.rank h z (gammaParent f g)
          ((BlockedMix.gammaBlock C Z T X Y).keep.before [.disj A B]) :=
  BlockedLeftDisj.gamma_first_descent f g h z hc
end

section
open BlockedLeftDisj
example {P : Type u} {A B C : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++C::Y)++[A]) D) (g : G P ((Z++C::T)++[B]) E) (h : G P I J) (z : At J C)
    (hc : PositionalCut.Clean h z (gammaParent f g)
      ((BlockedMix.gammaBlock C Z T X Y).keep.before [.disj A B])) :
    PositionalCut.Clean h z g ((BlockedMix.firstTag C Z T).before [B]) ∧
      PositionalCut.rank h z g ((BlockedMix.firstTag C Z T).before [B]) <
        PositionalCut.rank h z (gammaParent f g)
          ((BlockedMix.gammaBlock C Z T X Y).keep.before [.disj A B]) :=
  BlockedLeftDisj.gamma_second_descent f g h z hc
end

section
open BlockedLeftDisj
example {P : Type u} {A B C : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++C::Y)++[A]) D) (g : G P ((Z++C::T)++[B]) E) (h : G P I J) (z : At J C) :
    ofTerm (PositionalCut.cut h z (gammaParent f g)
      ((BlockedMix.gammaBlock C Z T X Y).keep.before [.disj A B])).denote =
      ofTerm (selectedParallel (BlockedMix.gammaBlock C Z T X Y).keep
        (BlockedMix.firstTag C X Y) (BlockedMix.firstTag C Z T)
        (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y)
        (PositionalCut.cut h z f ((BlockedMix.firstTag C X Y).before [A]))
        (PositionalCut.cut h z g ((BlockedMix.firstTag C Z T).before [B]))).denote :=
  BlockedLeftDisj.gamma_equation f g h z
end

section
open BlockedLeftDisj
example {P : Type u} {A B C : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++C::Y)++[A]) D) (g : G P ((Z++C::T)++[B]) E) (h : G P I J) (z : At J C)
    (hc : PositionalCut.Clean h z (BlockedLeftDisj.gammaParent f g)
      ((BlockedMix.gammaBlock C Z T X Y).keep.before [.disj A B]))
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank h z (BlockedLeftDisj.gammaParent f g)
        ((BlockedMix.gammaBlock C Z T X Y).keep.before [.disj A B]) →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (BlockedLeftDisj.gammaParent f g)
      ((BlockedMix.gammaBlock C Z T X Y).keep.before [.disj A B]) :=
  CutCommutation.blockedL_gammaDisj_rank_step f g h z hc ih
end

def literalChild (l : Literal Nat) : G Nat [.lit l,.lit l] [.lit l] :=
  G.thinL [] [.lit l] [.lit l] (.lit l) (G.identity l)

theorem literalChildCut (l : Literal Nat) : PositionalCut.Eliminated
    (G.identity l) (.here (.lit l) []) (literalChild l) (.here (.lit l) [.lit l]) :=
  PositionalCut.endomorphism_thin (Γ:=[]) (Θ:=[.lit l]) (Λ:=[.lit l]) (.lit l)
    (G.identity l) (G.identity l) rfl True.intro True.intro

def constantChild : G Empty [.top,.top] [.top] :=
  G.thinL [] [.top] [.top] .top G.topIdentity

theorem constantChildCut : PositionalCut.Eliminated (P:=Empty)
    G.topI (.here .top []) constantChild (.here .top [.top]) :=
  PositionalCut.top_thin [] [.top] [.top] G.topIdentity rfl ⟨True.intro,True.intro⟩

def twoTops : G Empty [.top] [.top,.top] := G.thinR [.top] [] [.top] .top G.topIdentity

def topPair : G Empty [.top,.top] [.top,.top] := G.thinL [] [.top] [.top,.top] .top twoTops

def threeTops : G Empty [.top,.top,.top] [.top,.top] :=
  G.thinL [.top] [.top] [.top,.top] .top topPair

def fourTops : G Empty [.top,.top,.top,.top] [.top,.top] :=
  G.thinL [.top] [.top,.top] [.top,.top] .top threeTops

theorem populatedChildCut : PositionalCut.Eliminated twoTops (.here .top [.top])
    fourTops (.there (.here .top [.top,.top])) :=
  PositionalCut.thin_thin [.top] [] [.top] [.top] [.top,.top] [.top,.top] .top G.topIdentity threeTops
    rfl rfl ⟨True.intro,True.intro⟩ (by repeat constructor)

example (l : Literal Nat) : PositionalCut.Eliminated (G.identity l) (.here (.lit l) [])
    (BlockedLeftDisj.gammaParent (X:=[]) (Y:=[]) (Z:=[]) (T:=[]) (literalChild l) (literalChild l))
    ((BlockedMix.gammaBlock (.lit l) [] [] [] []).keep.before [.disj (.lit l) (.lit l)]) :=
  CutCommutation.blockedL_gammaDisj_eliminated (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
    (literalChild l) (literalChild l) (G.identity l) (.here (.lit l) []) (literalChildCut l) (literalChildCut l)

example : PositionalCut.Eliminated (G.identity (P:=Nat) (.neg 0)) (.here (.lit (.neg 0)) [])
    (BlockedLeftDisj.gammaParent (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
      (literalChild (.neg 0)) (literalChild (.neg 0)))
    ((BlockedMix.gammaBlock (.lit (.neg 0)) [] [] [] []).keep.before [.disj (.lit (.neg 0)) (.lit (.neg 0))]) :=
  CutCommutation.blockedL_gammaDisj_eliminated (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
    (literalChild (.neg 0)) (literalChild (.neg 0)) (G.identity (.neg 0)) (.here (.lit (.neg 0)) [])
    (literalChildCut (.neg 0)) (literalChildCut (.neg 0))

example : PositionalCut.Eliminated (P:=Empty) G.topI (.here .top [])
    (BlockedLeftDisj.gammaParent (X:=[]) (Y:=[]) (Z:=[]) (T:=[]) constantChild constantChild)
    ((BlockedMix.gammaBlock .top [] [] [] []).keep.before [.disj .top .top]) :=
  CutCommutation.blockedL_gammaDisj_eliminated (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
    constantChild constantChild G.topI (.here .top []) constantChildCut constantChildCut

example : PositionalCut.Eliminated twoTops (.here .top [.top])
    (BlockedLeftDisj.gammaParent (X:=[.top]) (Y:=[.top]) (Z:=[.top]) (T:=[.top]) fourTops fourTops)
    ((BlockedMix.gammaBlock .top [.top] [.top] [.top] [.top]).keep.before [.disj .top .top]) :=
  CutCommutation.blockedL_gammaDisj_eliminated (X:=[.top]) (Y:=[.top]) (Z:=[.top]) (T:=[.top])
    fourTops fourTops twoTops (.here .top [.top]) populatedChildCut populatedChildCut

example :
    (((BlockedMix.gammaBlock (.disj .top .top : NormalForm Empty) [] [] [] []).extend [.disj .top .top]).route.get
      (At.shift ([.disj .top .top]++[.disj .top .top]) (.here (.disj .top .top) []))).index = 1 := by rfl

end BlockedLeftDisjChecks

#print axioms DosenPetric.Reduced.Gentzen.ContractionSplice.binary

#print axioms DosenPetric.Reduced.Gentzen.DoubleDisjSplice.equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedLeftDisj.canonical_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedLeftDisj.headParent_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedLeftDisj.selected_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedLeftDisj.gamma_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedLeftDisj.gamma_first_descent

#print axioms DosenPetric.Reduced.Gentzen.BlockedLeftDisj.gamma_second_descent

#print axioms DosenPetric.Reduced.Gentzen.CutCommutation.blockedL_gammaDisj_rank_step
