module

import DosenPetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
namespace BlockedGammaChecks

section
open BlockedMix
example {P : Type u} {C : NormalForm P} {X Y Z T Δ Λ I J : List (NormalForm P)}
    (f : G P (X++C::Y) Δ) (g : G P (Z++C::T) Λ) (h : G P I J) (z : At J C) :
    ofTerm (PositionalCut.cut h z (gammaParent f g) (gammaBlock C X Y Z T).keep).denote =
      ofTerm (parallel (gammaFirstRoute C X Y Z T) (gammaSecondRoute C X Y Z T)
        (PositionalCut.cut h z f (firstTag C X Y))
        (PositionalCut.cut h z g (firstTag C Z T))).denote :=
  BlockedMix.gamma_equation f g h z
end

section
open BlockedMix
example {P : Type u} {C : NormalForm P} {X Y Z T Δ Λ I J : List (NormalForm P)}
    (f : G P (X++C::Y) Δ) (g : G P (Z++C::T) Λ) (h : G P I J) (z : At J C)
    (hc : PositionalCut.Clean h z (BlockedMix.gammaParent f g) (BlockedMix.gammaBlock C X Y Z T).keep)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w <
        PositionalCut.rank h z (BlockedMix.gammaParent f g) (BlockedMix.gammaBlock C X Y Z T).keep →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (BlockedMix.gammaParent f g) (BlockedMix.gammaBlock C X Y Z T).keep :=
  CutCommutation.blockedL_gammaMix_rank_step f g h z hc ih
end

section
open BlockedMix
example {P : Type u} {C : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (X++C::Y)) (g : G P Θ (Z++C::T)) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (gammaRightParent f g) (gammaBlock C X Y Z T).keep h z).denote =
      ofTerm (rightParallel (gammaFirstRoute C X Y Z T) (gammaSecondRoute C X Y Z T)
        (PositionalCut.cut f (firstTag C X Y) h z)
        (PositionalCut.cut g (firstTag C Z T) h z)).denote :=
  BlockedMix.gamma_right_equation f g h z
end

section
open BlockedMix
example {P : Type u} {C : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (X++C::Y)) (g : G P Θ (Z++C::T)) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (BlockedMix.gammaRightParent f g) (BlockedMix.gammaBlock C X Y Z T).keep h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w <
        PositionalCut.rank (BlockedMix.gammaRightParent f g) (BlockedMix.gammaBlock C X Y Z T).keep h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (BlockedMix.gammaRightParent f g) (BlockedMix.gammaBlock C X Y Z T).keep h z :=
  CutCommutation.blockedR_gammaMix_rank_step f g h z hc ih
end

section
open BlockedConj
example {P : Type u} {A B C : NormalForm P} {X Y Z T Δ Λ I J : List (NormalForm P)}
    (f : G P (X++C::Y) (A::Δ)) (g : G P (Z++C::T) (B::Λ)) (h : G P I J) (z : At J C) :
    ofTerm (PositionalCut.cut h z (gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep).denote =
      ofTerm (parallel (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y)
        (PositionalCut.cut h z f (BlockedMix.firstTag C X Y))
        (PositionalCut.cut h z g (BlockedMix.firstTag C Z T))).denote :=
  BlockedConj.gamma_equation f g h z
end

section
open BlockedConj
example {P : Type u} {A B C : NormalForm P} {X Y Z T Δ Λ I J : List (NormalForm P)}
    (f : G P (X++C::Y) (A::Δ)) (g : G P (Z++C::T) (B::Λ)) (h : G P I J) (z : At J C)
    (hc : PositionalCut.Clean h z (BlockedConj.gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w <
        PositionalCut.rank h z (BlockedConj.gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (BlockedConj.gammaParent f g) (BlockedMix.gammaBlock C Z T X Y).keep :=
  CutCommutation.blockedL_gammaConj_rank_step f g h z hc ih
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

theorem constantChild : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    G.topIdentity (.here .top []) :=
  PositionalCut.top_thin [] [] [.top] G.topI rfl True.intro

example (l : Literal Nat) : PositionalCut.Eliminated (G.identity l) (.here (.lit l) [])
    (BlockedMix.gammaParent (X := []) (Y := []) (Z := []) (T := []) (G.identity l) (G.identity l))
    (BlockedMix.gammaBlock (.lit l) [] [] [] []).keep :=
  CutCommutation.blockedL_gammaMix_eliminated (X := []) (Y := []) (Z := []) (T := []) (G.identity l) (G.identity l)
    (G.identity l) (.here (.lit l) []) (identityChild l) (identityChild l)

example : PositionalCut.Eliminated (G.identity (P := Nat) (.neg 0)) (.here (.lit (.neg 0)) [])
    (BlockedMix.gammaParent (X := []) (Y := []) (Z := []) (T := [])
      (G.identity (.neg 0)) (G.identity (.neg 0)))
    (BlockedMix.gammaBlock (.lit (.neg 0)) [] [] [] []).keep :=
  CutCommutation.blockedL_gammaMix_eliminated (X := []) (Y := []) (Z := []) (T := []) (G.identity (.neg 0)) (G.identity (.neg 0))
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) (identityChild (.neg 0)) (identityChild (.neg 0))

example : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    (BlockedMix.gammaParent (X := []) (Y := []) (Z := []) (T := []) G.topIdentity G.topIdentity)
    (BlockedMix.gammaBlock .top [] [] [] []).keep :=
  CutCommutation.blockedL_gammaMix_eliminated (X := []) (Y := []) (Z := []) (T := []) G.topIdentity G.topIdentity G.topI (.here .top [])
    constantChild constantChild

example : PositionalCut.Eliminated twoTops (.here .top [.top])
    (BlockedMix.gammaParent (X := [.top]) (Y := [.top]) (Z := [.top]) (T := [.top]) rightPop rightPop)
    (BlockedMix.gammaBlock .top [.top] [.top] [.top] [.top]).keep :=
  CutCommutation.blockedL_gammaMix_eliminated (X := [.top]) (Y := [.top]) (Z := [.top]) (T := [.top]) rightPop rightPop twoTops (.here .top [.top])
    rightPopChild rightPopChild

example (l : Literal Nat) : PositionalCut.Eliminated (G.identity l) (.here (.lit l) [])
    (BlockedConj.gammaParent (X := []) (Y := []) (Z := []) (T := []) (G.identity l) (G.identity l))
    (BlockedMix.gammaBlock (.lit l) [] [] [] []).keep :=
  CutCommutation.blockedL_gammaConj_eliminated (X := []) (Y := []) (Z := []) (T := []) (G.identity l) (G.identity l)
    (G.identity l) (.here (.lit l) []) (identityChild l) (identityChild l)

example : PositionalCut.Eliminated (G.identity (P := Nat) (.neg 0)) (.here (.lit (.neg 0)) [])
    (BlockedConj.gammaParent (X := []) (Y := []) (Z := []) (T := [])
      (G.identity (.neg 0)) (G.identity (.neg 0)))
    (BlockedMix.gammaBlock (.lit (.neg 0)) [] [] [] []).keep :=
  CutCommutation.blockedL_gammaConj_eliminated (X := []) (Y := []) (Z := []) (T := []) (G.identity (.neg 0)) (G.identity (.neg 0))
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) (identityChild (.neg 0)) (identityChild (.neg 0))

example : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    (BlockedConj.gammaParent (X := []) (Y := []) (Z := []) (T := []) G.topIdentity G.topIdentity)
    (BlockedMix.gammaBlock .top [] [] [] []).keep :=
  CutCommutation.blockedL_gammaConj_eliminated (X := []) (Y := []) (Z := []) (T := []) G.topIdentity G.topIdentity G.topI (.here .top [])
    constantChild constantChild

example : PositionalCut.Eliminated twoTops (.here .top [.top])
    (BlockedConj.gammaParent (X := [.top]) (Y := [.top]) (Z := [.top]) (T := [.top]) rightPop rightPop)
    (BlockedMix.gammaBlock .top [.top] [.top] [.top] [.top]).keep :=
  CutCommutation.blockedL_gammaConj_eliminated (X := [.top]) (Y := [.top]) (Z := [.top]) (T := [.top]) rightPop rightPop twoTops (.here .top [.top])
    rightPopChild rightPopChild

example (l : Literal Nat) : PositionalCut.Eliminated
    (BlockedMix.gammaRightParent (X := []) (Y := []) (Z := []) (T := []) (G.identity l) (G.identity l))
    (BlockedMix.gammaBlock (.lit l) [] [] [] []).keep (G.identity l) (.here (.lit l) []) :=
  CutCommutation.blockedR_gammaMix_eliminated (X := []) (Y := []) (Z := []) (T := []) (G.identity l) (G.identity l)
    (G.identity l) (.here (.lit l) []) (identityChild l) (identityChild l)

example : PositionalCut.Eliminated
    (BlockedMix.gammaRightParent (X := []) (Y := []) (Z := []) (T := [])
      (G.identity (P := Nat) (.neg 0)) (G.identity (.neg 0)))
    (BlockedMix.gammaBlock (.lit (.neg 0)) [] [] [] []).keep
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) :=
  CutCommutation.blockedR_gammaMix_eliminated (X := []) (Y := []) (Z := []) (T := []) (G.identity (.neg 0)) (G.identity (.neg 0))
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) (identityChild (.neg 0)) (identityChild (.neg 0))

example : PositionalCut.Eliminated (P := Empty)
    (BlockedMix.gammaRightParent (X := []) (Y := []) (Z := []) (T := []) G.topI G.topI)
    (BlockedMix.gammaBlock .top [] [] [] []).keep G.topIdentity (.here .top []) :=
  CutCommutation.blockedR_gammaMix_eliminated (X := []) (Y := []) (Z := []) (T := []) G.topI G.topI G.topIdentity (.here .top [])
    constantChild constantChild

example : PositionalCut.Eliminated
    (BlockedMix.gammaRightParent (X := [.top]) (Y := [.top]) (Z := [.top]) (T := [.top]) leftPop leftPop)
    (BlockedMix.gammaBlock .top [.top] [.top] [.top] [.top]).keep topPair (.here .top [.top]) :=
  CutCommutation.blockedR_gammaMix_eliminated (X := [.top]) (Y := [.top]) (Z := [.top]) (T := [.top]) leftPop leftPop topPair (.here .top [.top])
    leftPopChild leftPopChild

end BlockedGammaChecks

#print axioms BlockedMix.gamma_equation

#print axioms BlockedMix.gamma_right_equation

#print axioms BlockedConj.gamma_equation

#print axioms BlockedConj.lifted_pair

#print axioms CutCommutation.blockedL_gammaMix_rank_step

#print axioms CutCommutation.blockedR_gammaMix_rank_step

#print axioms CutCommutation.blockedL_gammaConj_rank_step
