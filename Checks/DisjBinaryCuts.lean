module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
open DosenPetric.Reduced.Gentzen.DisjLogical
namespace DisjBinaryChecks

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (a : At Δ C) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (G.disjL f g) (a.before Λ) h z).denote =
      ofTerm (disjLLeftFirst a g (PositionalCut.cut f a h z)).denote :=
  DisjLogical.disjLLeftFirst_equation f g a h z

example {P : Type u} {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Δ C) (g : G P (B :: Θ) Λ) (k : G P (T ++ (A :: Γ)) (J ++ a.erase)) :
    (disjLLeftFirst a g k).cutCount = k.cutCount + g.cutCount :=
  DisjLogical.disjLLeftFirst_count a g k

example {P : Type u} {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Δ C) (g : G P (B :: Θ) Λ) (k : G P (T ++ (A :: Γ)) (J ++ a.erase)) :
    (disjLLeftFirst a g k).Atomized ↔ k.Atomized ∧ g.Atomized :=
  DisjLogical.disjLLeftFirst_atomized a g k

example {P : Type u} {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Δ C) (g : G P (B :: Θ) Λ) (k k' : G P (T ++ (A :: Γ)) (J ++ a.erase))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (disjLLeftFirst a g k).denote = ofTerm (disjLLeftFirst a g k').denote :=
  DisjLogical.disjLLeftFirst_congr a g k k' hk

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (a : At Δ C) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (G.disjL f g) (a.before Λ) h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank (G.disjL f g) (a.before Λ) h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (G.disjL f g) (a.before Λ) h z :=
  CutCommutation.disjL_left_first_rank_step f g a h z hc ih

example {P : Type u} {Γ Θ D Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) (C :: D)) (g : G P (B :: Θ) Λ) (h : G P (C :: T) J) :
    ofTerm (G.cut (G.disjL f g) h).denote = ofTerm (disjFirstNative (G.cut f h) g).denote :=
  disjFirstNative_equation f g h

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (a : At Λ C) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (G.disjL f g) (At.shift Δ a) h z).denote =
      ofTerm (disjLLeftSecond f a (PositionalCut.cut g a h z)).denote :=
  DisjLogical.disjLLeftSecond_equation f g a h z

example {P : Type u} {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (a : At Λ C) (k : G P (T ++ (B :: Θ)) (J ++ a.erase)) :
    (disjLLeftSecond f a k).cutCount = f.cutCount + k.cutCount :=
  DisjLogical.disjLLeftSecond_count f a k

example {P : Type u} {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (a : At Λ C) (k : G P (T ++ (B :: Θ)) (J ++ a.erase)) :
    (disjLLeftSecond f a k).Atomized ↔ f.Atomized ∧ k.Atomized :=
  DisjLogical.disjLLeftSecond_atomized f a k

example {P : Type u} {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (a : At Λ C) (k k' : G P (T ++ (B :: Θ)) (J ++ a.erase))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (disjLLeftSecond f a k).denote = ofTerm (disjLLeftSecond f a k').denote :=
  DisjLogical.disjLLeftSecond_congr f a k k' hk

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (a : At Λ C) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (G.disjL f g) (At.shift Δ a) h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank (G.disjL f g) (At.shift Δ a) h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (G.disjL f g) (At.shift Δ a) h z :=
  CutCommutation.disjL_left_second_rank_step f g a h z hc ih

example {P : Type u} {Γ Θ Δ E T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) (C :: E)) (h : G P (C :: T) J) :
    ofTerm (G.cut ((HeadRouting.front Δ E C).right (G.disjL f g)) h).denote =
      ofTerm (disjSecondNative f (G.cut g h)).denote :=
  disjSecondNative_equation f g h

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (h : G P I J) (z : At J C) (a : At Γ C) :
    ofTerm (PositionalCut.cut h z (G.disjL (Γ := Γ) (Θ := Θ) f g) (At.there (B := .disj A B) (a.before Θ))).denote =
      ofTerm (disjLRightFirst a g (PositionalCut.cut h z f a.there)).denote :=
  DisjLogical.disjLRightFirst_equation f g h z a

example {P : Type u} {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Γ C) (g : G P (B :: Θ) Λ) (k : G P (A :: (a.erase ++ I)) (Δ ++ D)) :
    (disjLRightFirst a g k).cutCount = k.cutCount + g.cutCount :=
  DisjLogical.disjLRightFirst_count a g k

example {P : Type u} {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Γ C) (g : G P (B :: Θ) Λ) (k : G P (A :: (a.erase ++ I)) (Δ ++ D)) :
    (disjLRightFirst a g k).Atomized ↔ k.Atomized ∧ g.Atomized :=
  DisjLogical.disjLRightFirst_atomized a g k

example {P : Type u} {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Γ C) (g : G P (B :: Θ) Λ) (k k' : G P (A :: (a.erase ++ I)) (Δ ++ D))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (disjLRightFirst a g k).denote = ofTerm (disjLRightFirst a g k').denote :=
  DisjLogical.disjLRightFirst_congr a g k k' hk

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (h : G P I J) (z : At J C) (a : At Γ C)
    (hc : PositionalCut.Clean h z (G.disjL (Γ := Γ) (Θ := Θ) f g) (At.there (B := .disj A B) (a.before Θ)))
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank h z (G.disjL (Γ := Γ) (Θ := Θ) f g) (At.there (B := .disj A B) (a.before Θ)) →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (G.disjL (Γ := Γ) (Θ := Θ) f g) (At.there (B := .disj A B) (a.before Θ)) :=
  CutCommutation.disjL_right_first_rank_step f g h z a hc ih

example {P : Type u} {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: C :: Γ) Δ) (g : G P (B :: Θ) Λ) (h : G P I (C :: D)) :
    ofTerm (G.cut h ((HeadRouting.front [.disj A B] (Γ ++ Θ) C).left (G.disjL (Γ := C :: Γ) (Θ := Θ) f g))).denote =
      ofTerm (disjRightFirstNative (G.cut h ((HeadRouting.front [A] Γ C).left f)) g).denote :=
  disjRightFirstNative_equation f g h

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (h : G P I J) (z : At J C) (a : At Θ C) :
    ofTerm (PositionalCut.cut h z (G.disjL f g) (At.shift (.disj A B :: Γ) a)).denote =
      ofTerm (disjLRightSecond f a (PositionalCut.cut h z g a.there)).denote :=
  DisjLogical.disjLRightSecond_equation f g h z a

example {P : Type u} {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (a : At Θ C) (k : G P (B :: (a.erase ++ I)) (Λ ++ D)) :
    (disjLRightSecond f a k).cutCount = f.cutCount + k.cutCount :=
  DisjLogical.disjLRightSecond_count f a k

example {P : Type u} {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (a : At Θ C) (k : G P (B :: (a.erase ++ I)) (Λ ++ D)) :
    (disjLRightSecond f a k).Atomized ↔ f.Atomized ∧ k.Atomized :=
  DisjLogical.disjLRightSecond_atomized f a k

example {P : Type u} {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (a : At Θ C) (k k' : G P (B :: (a.erase ++ I)) (Λ ++ D))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (disjLRightSecond f a k).denote = ofTerm (disjLRightSecond f a k').denote :=
  DisjLogical.disjLRightSecond_congr f a k k' hk

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (h : G P I J) (z : At J C) (a : At Θ C)
    (hc : PositionalCut.Clean h z (G.disjL f g) (At.shift (.disj A B :: Γ) a))
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank h z (G.disjL f g) (At.shift (.disj A B :: Γ) a) →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (G.disjL f g) (At.shift (.disj A B :: Γ) a) :=
  CutCommutation.disjL_right_second_rank_step f g h z a hc ih

example {P : Type u} {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: C :: Θ) Λ) (h : G P I (C :: D)) :
    ofTerm (G.cut h ((HeadRouting.front (.disj A B :: Γ) Θ C).left (G.disjL f g))).denote =
      ofTerm (disjRightSecondNative f (G.cut h ((HeadRouting.front [B] Θ C).left g))).denote :=
  disjRightSecondNative_equation f g h

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

example (l : Literal Nat) : PositionalCut.Eliminated
    (G.disjL (G.identity l) (G.identity l)) (.here (.lit l) [.lit l]) (G.identity l) (.here (.lit l) []) :=
  CutCommutation.disjL_left_first_eliminated (G.identity l) (G.identity l) (.here (.lit l) []) (G.identity l) (.here (.lit l) []) rfl True.intro (identityChild l)

example : PositionalCut.Eliminated
    (G.disjL (G.identity (P := Nat) (.neg 0)) (G.identity (.neg 0))) (.here (.lit (.neg 0)) [.lit (.neg 0)])
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) :=
  CutCommutation.disjL_left_first_eliminated (G.identity (.neg 0)) (G.identity (.neg 0)) (.here (.lit (.neg 0)) [])
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) rfl True.intro (identityChild (.neg 0))

example : PositionalCut.Eliminated (G.disjL twoTops G.topIdentity) (.here .top [.top,.top]) G.topIdentity (.here .top []) :=
  CutCommutation.disjL_left_first_eliminated twoTops G.topIdentity (.here .top [.top]) G.topIdentity (.here .top [])
    rfl ⟨True.intro,True.intro⟩ leftConstantChild

example : PositionalCut.Eliminated (G.disjL leftPop topPair) ((At.there (.here .top [.top])).before [.top,.top]) topPair (.here .top [.top]) :=
  CutCommutation.disjL_left_first_eliminated leftPop topPair (.there (.here .top [.top])) topPair (.here .top [.top])
    rfl ⟨True.intro,⟨True.intro,⟨True.intro,True.intro⟩⟩⟩ leftPopChild

example (l : Literal Nat) : PositionalCut.Eliminated
    (G.disjL (G.identity l) (G.identity l)) (.there (.here (.lit l) [])) (G.identity l) (.here (.lit l) []) :=
  CutCommutation.disjL_left_second_eliminated (G.identity l) (G.identity l) (.here (.lit l) []) (G.identity l) (.here (.lit l) []) rfl True.intro (identityChild l)

example : PositionalCut.Eliminated
    (G.disjL (G.identity (P := Nat) (.neg 0)) (G.identity (.neg 0))) (.there (.here (.lit (.neg 0)) []))
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) :=
  CutCommutation.disjL_left_second_eliminated (G.identity (.neg 0)) (G.identity (.neg 0)) (.here (.lit (.neg 0)) [])
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) rfl True.intro (identityChild (.neg 0))

example : PositionalCut.Eliminated (G.disjL G.topIdentity twoTops) (.there (.here .top [.top])) G.topIdentity (.here .top []) :=
  CutCommutation.disjL_left_second_eliminated G.topIdentity twoTops (.here .top [.top]) G.topIdentity (.here .top [])
    rfl ⟨True.intro,True.intro⟩ leftConstantChild

example : PositionalCut.Eliminated (G.disjL topPair leftPop) (At.shift [.top,.top] (.there (.here .top [.top]))) topPair (.here .top [.top]) :=
  CutCommutation.disjL_left_second_eliminated topPair leftPop (.there (.here .top [.top])) topPair (.here .top [.top])
    rfl ⟨True.intro,⟨True.intro,⟨True.intro,True.intro⟩⟩⟩ leftPopChild

example (l : Literal Nat) : PositionalCut.Eliminated (doubled l) (.here (.lit l) [.lit l])
    (G.disjL (repeatedInput l) (G.identity l)) (.there (.here (.lit l) [])) :=
  CutCommutation.disjL_right_first_eliminated (repeatedInput l) (G.identity l) (doubled l) (.here (.lit l) [.lit l]) (.here (.lit l) [])
    rfl True.intro (repeatedChild l)

example : PositionalCut.Eliminated (doubled (.neg 0)) (.here (.lit (.neg 0)) [.lit (.neg 0)])
    (G.disjL (repeatedInput (.neg 0)) (G.identity (.neg 0))) (.there (.here (.lit (.neg 0)) [])) :=
  CutCommutation.disjL_right_first_eliminated (repeatedInput (.neg 0)) (G.identity (.neg 0))
    (doubled (.neg 0)) (.here (.lit (.neg 0)) [.lit (.neg 0)]) (.here (.lit (.neg 0)) []) rfl True.intro (repeatedChild (.neg 0))

example : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    (G.disjL (G.thinL [.top] [] [.top] .top G.topIdentity) G.topIdentity) (.there (.here .top [])) :=
  CutCommutation.disjL_right_first_eliminated (G.thinL [.top] [] [.top] .top G.topIdentity) G.topIdentity G.topI (.here .top []) (.here .top [])
    rfl ⟨True.intro,True.intro⟩ rightConstantChild

example : PositionalCut.Eliminated twoTops (.here .top [.top]) (G.disjL rightPop topPair) (.there ((At.here .top [.top]).before [.top])) :=
  CutCommutation.disjL_right_first_eliminated rightPop topPair twoTops (.here .top [.top]) (.here .top [.top])
    rfl ⟨True.intro,⟨True.intro,⟨True.intro,True.intro⟩⟩⟩ rightPopChild

example (l : Literal Nat) : PositionalCut.Eliminated (doubled l) (.here (.lit l) [.lit l])
    (G.disjL (G.identity l) (repeatedInput l)) (.there (.here (.lit l) [])) :=
  CutCommutation.disjL_right_second_eliminated (G.identity l) (repeatedInput l) (doubled l) (.here (.lit l) [.lit l]) (.here (.lit l) [])
    rfl True.intro (repeatedChild l)

example : PositionalCut.Eliminated (doubled (.neg 0)) (.here (.lit (.neg 0)) [.lit (.neg 0)])
    (G.disjL (G.identity (.neg 0)) (repeatedInput (.neg 0))) (.there (.here (.lit (.neg 0)) [])) :=
  CutCommutation.disjL_right_second_eliminated (G.identity (.neg 0)) (repeatedInput (.neg 0))
    (doubled (.neg 0)) (.here (.lit (.neg 0)) [.lit (.neg 0)]) (.here (.lit (.neg 0)) []) rfl True.intro (repeatedChild (.neg 0))

example : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    (G.disjL G.topIdentity (G.thinL [.top] [] [.top] .top G.topIdentity)) (.there (.here .top [])) :=
  CutCommutation.disjL_right_second_eliminated G.topIdentity (G.thinL [.top] [] [.top] .top G.topIdentity) G.topI (.here .top []) (.here .top [])
    rfl ⟨True.intro,True.intro⟩ rightConstantChild

example : PositionalCut.Eliminated twoTops (.here .top [.top]) (G.disjL topPair rightPop) (At.shift [.disj .top .top,.top] (.here .top [.top])) :=
  CutCommutation.disjL_right_second_eliminated topPair rightPop twoTops (.here .top [.top]) (.here .top [.top])
    rfl ⟨True.intro,⟨True.intro,⟨True.intro,True.intro⟩⟩⟩ rightPopChild

end DisjBinaryChecks

#print axioms DisjLogical.disjL_left_first_core

#print axioms DisjLogical.sourceConj_swap

#print axioms DisjLogical.disjL_right_second_core

#print axioms DisjLogical.disjL_right_first_core

#print axioms CutCommutation.disjL_left_first_rank_step

#print axioms CutCommutation.disjL_left_second_rank_step

#print axioms CutCommutation.disjL_right_first_rank_step

#print axioms CutCommutation.disjL_right_second_rank_step

#print axioms DisjLogical.disjLLeftFirst_equation

#print axioms DisjLogical.disjLLeftSecond_equation

#print axioms DisjLogical.disjLRightFirst_equation

#print axioms DisjLogical.disjLRightSecond_equation
