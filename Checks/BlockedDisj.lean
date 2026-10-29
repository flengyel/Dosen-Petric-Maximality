module

import DosenPetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
namespace BlockedDisjChecks

section
open BlockedDisj
example {P : Type u} {A B C : NormalForm P} {F U X Y Z T I J : List (NormalForm P)}
    (f : G P (F++[A]) (X++C::Y)) (g : G P (U++[B]) (Z++C::T)) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep h z).denote =
      ofTerm (parallel (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y)
        (PositionalCut.cut f (BlockedMix.firstTag C X Y) h z)
        (PositionalCut.cut g (BlockedMix.firstTag C Z T) h z)).denote :=
  BlockedDisj.gamma_equation f g h z
end

section
open BlockedDisj
example {P : Type u} {A B C : NormalForm P} {F U X Y Z T I J : List (NormalForm P)}
    (f : G P (F++[A]) (X++C::Y)) (g : G P (U++[B]) (Z++C::T)) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (BlockedDisj.gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w <
        PositionalCut.rank (BlockedDisj.gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (BlockedDisj.gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep h z :=
  CutCommutation.blockedR_gammaDisj_rank_step f g h z hc ih
end

theorem identityChild (l : Literal Nat) : PositionalCut.Eliminated (G.identity l) (.here (.lit l) [])
    (G.identity l) (.here (.lit l) []) :=
  ⟨G.identity l,rfl,True.intro,(CutBase.identity_identity l).symm⟩

def doubled (l : Literal Nat) : G Nat [.lit l] [.lit l,.lit l] :=
  G.thinR [.lit l] [] [.lit l] (.lit l) (G.identity l)
def repeatedInput (l : Literal Nat) : G Nat [.lit l,.lit l] [.lit l] :=
  G.thinL [.lit l] [] [.lit l] (.lit l) (G.identity l)

theorem repeatedChild (l : Literal Nat) : PositionalCut.Eliminated (doubled l) (.here (.lit l) [.lit l])
    (repeatedInput l) (.there (.here (.lit l) [])) :=
  PositionalCut.thin_thin [.lit l] [] [.lit l] [.lit l] [] [.lit l] (.lit l)
    (G.identity l) (G.identity l) rfl rfl True.intro True.intro

def twoTops : G Empty [.top] [.top,.top] := G.thinR [.top] [] [.top] .top G.topIdentity
def topPair : G Empty [.top,.top] [.top,.top] := G.thinL [] [.top] [.top,.top] .top twoTops
def leftPop : G Empty [.top,.top] [.top,.top,.top] := G.thinR [.top,.top] [.top] [.top] .top topPair
def rightPop : G Empty [.top,.top,.top] [.top,.top] := G.thinL [.top] [.top] [.top,.top] .top topPair

theorem leftConstantChild : PositionalCut.Eliminated twoTops (.here .top [.top])
    G.topIdentity (.here .top []) :=
  PositionalCut.thin_thin [.top] [] [.top] [] [] [.top] .top G.topIdentity G.topI
    rfl rfl ⟨True.intro,True.intro⟩ True.intro

theorem rightConstantChild : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    (G.thinL [.top] [] [.top] .top G.topIdentity) (.there (.here .top [])) :=
  PositionalCut.top_thin [.top] [] [.top] G.topIdentity rfl ⟨True.intro,True.intro⟩

theorem leftPopChild : PositionalCut.Eliminated leftPop (.there (.here .top [.top]))
    topPair (.here .top [.top]) :=
  PositionalCut.thin_thin [.top,.top] [.top] [.top] [] [.top] [.top,.top] .top topPair twoTops rfl rfl
    ⟨True.intro,⟨True.intro,⟨True.intro,True.intro⟩⟩⟩ ⟨True.intro,⟨True.intro,True.intro⟩⟩

theorem rightPopChild : PositionalCut.Eliminated twoTops (.here .top [.top])
    rightPop (.there (.here .top [.top])) :=
  PositionalCut.thin_thin [.top] [] [.top] [.top] [.top] [.top,.top] .top G.topIdentity topPair rfl rfl
    ⟨True.intro,True.intro⟩ ⟨True.intro,⟨True.intro,⟨True.intro,True.intro⟩⟩⟩

theorem constantChild : PositionalCut.Eliminated (P := Empty) G.topIdentity (.here .top [])
    G.topIdentity (.here .top []) :=
  PositionalCut.endomorphism_thin (Γ := []) (Θ := []) (Λ := [.top])
    .top G.topIdentity G.topI rfl True.intro True.intro

example (l : Literal Nat) : PositionalCut.Eliminated
    (BlockedDisj.gammaParent (F := []) (U := []) (X := []) (Y := []) (Z := []) (T := [])
      (G.identity l) (G.identity l))
    (BlockedMix.gammaBlock (.lit l) [] [] [] []).keep (G.identity l) (.here (.lit l) []) :=
  CutCommutation.blockedR_gammaDisj_eliminated (F := []) (U := []) (X := []) (Y := []) (Z := []) (T := [])
    (G.identity l) (G.identity l) (G.identity l) (.here (.lit l) []) (identityChild l) (identityChild l)

example : PositionalCut.Eliminated
    (BlockedDisj.gammaParent (F := []) (U := []) (X := []) (Y := []) (Z := []) (T := [])
      (G.identity (P := Nat) (.neg 0)) (G.identity (.neg 0)))
    (BlockedMix.gammaBlock (.lit (.neg 0)) [] [] [] []).keep
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) :=
  CutCommutation.blockedR_gammaDisj_eliminated (F := []) (U := []) (X := []) (Y := []) (Z := []) (T := [])
    (G.identity (.neg 0)) (G.identity (.neg 0)) (G.identity (.neg 0)) (.here (.lit (.neg 0)) [])
    (identityChild (.neg 0)) (identityChild (.neg 0))

example : PositionalCut.Eliminated (P := Empty)
    (BlockedDisj.gammaParent (F := []) (U := []) (X := []) (Y := []) (Z := []) (T := [])
      G.topIdentity G.topIdentity)
    (BlockedMix.gammaBlock .top [] [] [] []).keep G.topIdentity (.here .top []) :=
  CutCommutation.blockedR_gammaDisj_eliminated (F := []) (U := []) (X := []) (Y := []) (Z := []) (T := [])
    G.topIdentity G.topIdentity G.topIdentity (.here .top []) constantChild constantChild

example : PositionalCut.Eliminated (P := Empty)
    (BlockedDisj.gammaParent (F := [.top]) (U := [.top])
      (X := [.top]) (Y := [.top]) (Z := [.top]) (T := [.top]) leftPop leftPop)
    (BlockedMix.gammaBlock .top [.top] [.top] [.top] [.top]).keep topPair (.here .top [.top]) :=
  CutCommutation.blockedR_gammaDisj_eliminated (F := [.top]) (U := [.top])
    (X := [.top]) (Y := [.top]) (Z := [.top]) (T := [.top])
    leftPop leftPop topPair (.here .top [.top]) leftPopChild leftPopChild

end BlockedDisjChecks

#print axioms DosenPetric.Reduced.Gentzen.BlockedDisj.right_shared_splice

#print axioms DosenPetric.Reduced.Gentzen.BlockedDisj.headParent_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedDisj.gamma_equation

#print axioms DosenPetric.Reduced.Gentzen.CutCommutation.blockedR_gammaDisj_rank_step
