module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
open DosenPetric.Reduced.Gentzen.BinaryLogical
namespace ConjLeftSecondChecks

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (a : At Λ C) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (G.conjR (Δ := Δ) (Λ := Λ) f g)
      (At.shift (.conj A B :: Δ) a) h z).denote =
      ofTerm (conjRLeftSecond f a (PositionalCut.cut g a.there h z)).denote :=
  BinaryLogical.conjRLeftSecond_equation f g a h z

example {P : Type u} {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (a : At Λ C) (k : G P (T ++ Θ) (J ++ (B :: a.erase))) :
    (conjRLeftSecond f a k).cutCount = f.cutCount + k.cutCount :=
  BinaryLogical.conjRLeftSecond_count f a k

example {P : Type u} {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (a : At Λ C) (k : G P (T ++ Θ) (J ++ (B :: a.erase))) :
    (conjRLeftSecond f a k).Atomized ↔ f.Atomized ∧ k.Atomized :=
  BinaryLogical.conjRLeftSecond_atomized f a k

example {P : Type u} {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (a : At Λ C) (k k' : G P (T ++ Θ) (J ++ (B :: a.erase)))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (conjRLeftSecond f a k).denote = ofTerm (conjRLeftSecond f a k').denote :=
  BinaryLogical.conjRLeftSecond_congr f a k k' hk

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (a : At Λ C) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (G.conjR (Δ := Δ) (Λ := Λ) f g) (At.shift (.conj A B :: Δ) a) h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank (G.conjR (Δ := Δ) (Λ := Λ) f g)
        (At.shift (.conj A B :: Δ) a) h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (G.conjR (Δ := Δ) (Λ := Λ) f g) (At.shift (.conj A B :: Δ) a) h z :=
  CutCommutation.conjR_left_second_rank_step f g a h z hc ih

def retainedSecondNative {P : Type u} {Γ Θ Δ E T J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A :: Δ)) (k : G P (T ++ Θ) (J ++ (B :: E))) :
    G P (T ++ (Γ ++ Θ)) (J ++ (.conj A B :: (Δ ++ E))) :=
  (HeadRouting.front J (Δ ++ E) (.conj A B)).inverse.right
    (((BinaryMix.swapBlocks Δ J E).consFixed (.conj A B)).right
      ((BinaryMix.swapBlocks Γ T Θ).left
        (G.conjR f ((HeadRouting.front J E B).right k))))

example {P : Type u} {Γ Θ Δ E T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: C :: E)) (h : G P (C :: T) J) :
    ofTerm (G.cut ((HeadRouting.front (.conj A B :: Δ) E C).right
      (G.conjR (Δ := Δ) (Λ := C :: E) f g)) h).denote =
      ofTerm (retainedSecondNative f (G.cut ((HeadRouting.front [B] E C).right g) h)).denote :=
  conjLeftSecondNative_equation f g h

def doubled (l : Literal Nat) : G Nat [.lit l] [.lit l,.lit l] :=
  G.thinR [.lit l] [.lit l] [] (.lit l) (G.identity l)

theorem literalChild (l : Literal Nat) : PositionalCut.Eliminated (doubled l)
    (.there (.here (.lit l) [])) (G.identity l) (.here (.lit l) []) :=
  PositionalCut.thin_endomorphism (Γ := [.lit l]) (Δ := [.lit l]) (Λ := []) (.lit l)
    (G.identity l) (G.identity l) rfl True.intro True.intro

example (l : Literal Nat) : PositionalCut.Eliminated
    (G.conjR (G.identity l) (doubled l)) (.there (.here (.lit l) []))
    (G.identity l) (.here (.lit l) []) :=
  CutCommutation.conjR_left_second_eliminated (G.identity l) (doubled l) (.here (.lit l) [])
    (G.identity l) (.here (.lit l) []) rfl True.intro (literalChild l)

example : PositionalCut.Eliminated
    (G.conjR (G.identity (.neg 0)) (doubled (.neg 0))) (.there (.here (.lit (.neg 0)) []))
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) :=
  CutCommutation.conjR_left_second_eliminated (G.identity (.neg 0)) (doubled (.neg 0))
    (.here (.lit (.neg 0)) []) (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) rfl True.intro (literalChild (.neg 0))

def constantG : G Empty [] [.top,.top] := G.thinR [] [.top] [] .top G.topI

theorem constantChild : PositionalCut.Eliminated constantG (.there (.here .top []))
    G.topIdentity (.here .top []) :=
  PositionalCut.thin_thin [] [.top] [] [] [] [.top] .top G.topI G.topI rfl rfl True.intro True.intro

example : PositionalCut.Eliminated (G.conjR G.topI constantG) (.there (.here .top []))
    G.topIdentity (.here .top []) :=
  CutCommutation.conjR_left_second_eliminated G.topI constantG (.here .top [])
    G.topIdentity (.here .top []) rfl True.intro constantChild

def twoTops : G Empty [.top] [.top,.top] := G.thinR [.top] [] [.top] .top G.topIdentity
def populatedG : G Empty [.top] [.top,.top,.top] := G.thinR [.top] [.top] [.top] .top twoTops
def populatedH : G Empty [.top,.top] [.top,.top] := G.thinL [] [.top] [.top,.top] .top twoTops

theorem populatedChild : PositionalCut.Eliminated populatedG (.there (.here .top [.top]))
    populatedH (.here .top [.top]) :=
  PositionalCut.thin_thin [.top] [.top] [.top] [] [.top] [.top,.top] .top twoTops twoTops
    rfl rfl ⟨True.intro,⟨True.intro,True.intro⟩⟩ ⟨True.intro,⟨True.intro,True.intro⟩⟩

example : PositionalCut.Eliminated (G.conjR twoTops populatedG) (.there (.there (.here .top [.top])))
    populatedH (.here .top [.top]) :=
  CutCommutation.conjR_left_second_eliminated twoTops populatedG (.here .top [.top])
    populatedH (.here .top [.top]) rfl ⟨True.intro,⟨True.intro,True.intro⟩⟩ populatedChild

-- The selected second-child tag is below another fixed residual output.
example (l : Literal Nat) :
    ofTerm (PositionalCut.cut
      (G.conjR (G.identity l) (G.thinR [.lit l] [.lit l] [.lit l] .top (doubled l)))
      (.there (.there (.here (.lit l) []))) (G.identity l) (.here (.lit l) [])).denote =
    ofTerm (conjRLeftSecond (G.identity l) (.there (.here (.lit l) []))
      (PositionalCut.cut (G.thinR [.lit l] [.lit l] [.lit l] .top (doubled l))
        (.there (.there (.here (.lit l) []))) (G.identity l) (.here (.lit l) []))).denote := by
  simpa only [At.shift] using conjRLeftSecond_equation
    (G.identity l) (G.thinR [.lit l] [.lit l] [.lit l] .top (doubled l))
    (.there (.here (.lit l) [])) (G.identity l) (.here (.lit l) [])

end ConjLeftSecondChecks

#print axioms BinaryLogical.selectedMixedSecond_swap

#print axioms BinaryLogical.conjR_left_second_core

#print axioms BinaryMix.swapBlocks_split

#print axioms BinaryLogical.conjLeftSecondNative_equation

#print axioms BinaryLogical.conjRLeftSecond_equation

#print axioms CutCommutation.conjR_left_second_rank_step
