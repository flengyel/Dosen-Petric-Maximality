module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
open DosenPetric.Reduced.Gentzen.BinaryLogical
namespace ConjLeftFirstChecks

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (a : At Δ C) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (G.conjR (Δ := Δ) (Λ := Λ) f g) (At.there (B := .conj A B) (a.before Λ)) h z).denote =
      ofTerm (conjRLeftFirst a g (PositionalCut.cut f a.there h z)).denote :=
  BinaryLogical.conjRLeftFirst_equation f g a h z

example {P : Type u} {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Δ C) (g : G P Θ (B :: Λ)) (k : G P (T ++ Γ) (J ++ (A :: a.erase))) :
    (conjRLeftFirst a g k).cutCount = k.cutCount + g.cutCount :=
  BinaryLogical.conjRLeftFirst_count a g k

example {P : Type u} {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Δ C) (g : G P Θ (B :: Λ)) (k : G P (T ++ Γ) (J ++ (A :: a.erase))) :
    (conjRLeftFirst a g k).Atomized ↔ k.Atomized ∧ g.Atomized :=
  BinaryLogical.conjRLeftFirst_atomized a g k

example {P : Type u} {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Δ C) (g : G P Θ (B :: Λ)) (k k' : G P (T ++ Γ) (J ++ (A :: a.erase)))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (conjRLeftFirst a g k).denote = ofTerm (conjRLeftFirst a g k').denote :=
  BinaryLogical.conjRLeftFirst_congr a g k k' hk

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (a : At Δ C) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (G.conjR (Δ := Δ) (Λ := Λ) f g) (At.there (B := .conj A B) (a.before Λ)) h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank (G.conjR (Δ := Δ) (Λ := Λ) f g) (At.there (B := .conj A B) (a.before Λ)) h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (G.conjR (Δ := Δ) (Λ := Λ) f g) (At.there (B := .conj A B) (a.before Λ)) h z :=
  CutCommutation.conjR_left_first_rank_step f g a h z hc ih

def doubled (l : Literal Nat) : G Nat [.lit l] [.lit l,.lit l] :=
  G.thinR [.lit l] [.lit l] [] (.lit l) (G.identity l)

theorem literalChild (l : Literal Nat) : PositionalCut.Eliminated (doubled l)
    (.there (.here (.lit l) [])) (G.identity l) (.here (.lit l) []) :=
  PositionalCut.thin_endomorphism (Γ := [.lit l]) (Δ := [.lit l]) (Λ := []) (.lit l) (G.identity l) (G.identity l) rfl True.intro True.intro

example (l : Literal Nat) : PositionalCut.Eliminated
    (G.conjR (doubled l) (G.identity l)) (.there (.here (.lit l) []))
    (G.identity l) (.here (.lit l) []) :=
  CutCommutation.conjR_left_first_eliminated (doubled l) (G.identity l) (.here (.lit l) [])
    (G.identity l) (.here (.lit l) []) rfl True.intro (literalChild l)

example : PositionalCut.Eliminated
    (G.conjR (doubled (.neg 0)) (G.identity (.neg 0))) (.there (.here (.lit (.neg 0)) []))
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) :=
  CutCommutation.conjR_left_first_eliminated (doubled (.neg 0)) (G.identity (.neg 0))
    (.here (.lit (.neg 0)) []) (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) rfl True.intro (literalChild (.neg 0))

def constantF : G Empty [] [.top,.top] := G.thinR [] [.top] [] .top G.topI

theorem constantChild : PositionalCut.Eliminated constantF (.there (.here .top []))
    G.topIdentity (.here .top []) :=
  PositionalCut.thin_thin [] [.top] [] [] [] [.top] .top G.topI G.topI rfl rfl True.intro True.intro

example : PositionalCut.Eliminated (G.conjR constantF G.topI) (.there (.here .top []))
    G.topIdentity (.here .top []) :=
  CutCommutation.conjR_left_first_eliminated constantF G.topI (.here .top [])
    G.topIdentity (.here .top []) rfl True.intro constantChild

def twoTops : G Empty [.top] [.top,.top] := G.thinR [.top] [] [.top] .top G.topIdentity
def populatedF : G Empty [.top] [.top,.top,.top] := G.thinR [.top] [.top] [.top] .top twoTops
def populatedH : G Empty [.top,.top] [.top,.top] := G.thinL [] [.top] [.top,.top] .top twoTops

theorem populatedChild : PositionalCut.Eliminated populatedF (.there (.here .top [.top]))
    populatedH (.here .top [.top]) :=
  PositionalCut.thin_thin [.top] [.top] [.top] [] [.top] [.top,.top] .top twoTops twoTops
    rfl rfl ⟨True.intro,⟨True.intro,True.intro⟩⟩ ⟨True.intro,⟨True.intro,True.intro⟩⟩

example : PositionalCut.Eliminated (G.conjR populatedF twoTops) (.there (.here .top [.top,.top]))
    populatedH (.here .top [.top]) :=
  CutCommutation.conjR_left_first_eliminated populatedF twoTops (.here .top [.top])
    populatedH (.here .top [.top]) rfl ⟨True.intro,⟨True.intro,True.intro⟩⟩ populatedChild

-- A fixed output lies between the retained principal and selected occurrence.
example (l : Literal Nat) :
    ofTerm (PositionalCut.cut
      (G.conjR (G.thinR [.lit l] [.lit l] [.lit l] .top (doubled l)) (G.identity l))
      (.there (.there (.here (.lit l) []))) (G.identity l) (.here (.lit l) [])).denote =
    ofTerm (conjRLeftFirst (.there (.here (.lit l) [])) (G.identity l)
      (PositionalCut.cut (G.thinR [.lit l] [.lit l] [.lit l] .top (doubled l))
        (.there (.there (.here (.lit l) []))) (G.identity l) (.here (.lit l) []))).denote := by
  simpa only [At.before,List.append_nil,List.nil_append] using conjRLeftFirst_equation
    (G.thinR [.lit l] [.lit l] [.lit l] .top (doubled l)) (G.identity l)
    (.there (.here (.lit l) [])) (G.identity l) (.here (.lit l) [])

example {P : Type u} {Γ Θ D Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: C :: D)) (g : G P Θ (B :: Λ)) (h : G P (C :: T) J) :
    ofTerm (G.cut ((HeadRouting.front [.conj A B] (D ++ Λ) C).right
      (G.conjR (Δ := C :: D) (Λ := Λ) f g)) h).denote =
      ofTerm (conjLeftFirstNative (G.cut ((HeadRouting.front [A] D C).right f) h) g).denote :=
  conjLeftFirstNative_equation f g h

end ConjLeftFirstChecks

#print axioms BinaryLogical.splice_distRight

#print axioms BinaryLogical.selectedMixed_eq

#print axioms BinaryLogical.conjR_left_first_core

#print axioms BinaryLogical.conjLeftFirstNative_equation

#print axioms BinaryLogical.conjRLeftFirst_equation

#print axioms CutCommutation.conjR_left_first_rank_step
