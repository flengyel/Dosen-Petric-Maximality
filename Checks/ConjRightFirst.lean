module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
open DosenPetric.Reduced.Gentzen.BinaryLogical
namespace ConjFirstChecks

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I J) (z : At J C) (a : At Γ C) :
    ofTerm (PositionalCut.cut h z (G.conjR f g) (a.before Θ)).denote =
      ofTerm (conjRRightFirst a g (PositionalCut.cut h z f a)).denote :=
  BinaryLogical.conjRRightFirst_equation f g h z a

example {P : Type u} {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Γ C) (g : G P Θ (B :: Λ)) (k : G P (a.erase ++ I) ((A :: Δ) ++ D)) :
    (conjRRightFirst a g k).cutCount = k.cutCount + g.cutCount :=
  BinaryLogical.conjRRightFirst_count a g k

example {P : Type u} {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Γ C) (g : G P Θ (B :: Λ)) (k : G P (a.erase ++ I) ((A :: Δ) ++ D)) :
    (conjRRightFirst a g k).Atomized ↔ k.Atomized ∧ g.Atomized :=
  BinaryLogical.conjRRightFirst_atomized a g k

example {P : Type u} {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Γ C) (g : G P Θ (B :: Λ)) (k k' : G P (a.erase ++ I) ((A :: Δ) ++ D))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (conjRRightFirst a g k).denote = ofTerm (conjRRightFirst a g k').denote :=
  BinaryLogical.conjRRightFirst_congr a g k k' hk

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I J) (z : At J C) (a : At Γ C)
    (hc : PositionalCut.Clean h z (G.conjR f g) (a.before Θ))
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank h z (G.conjR f g) (a.before Θ) →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (G.conjR f g) (a.before Θ) :=
  CutCommutation.conjR_right_first_rank_step f g h z a hc ih

-- This is the exact retained native candidate, with its original two exchanges.
def retainedFirstNative {P : Type u} {Γ Θ Δ Λ I D : List (NormalForm P)} {A B : NormalForm P}
    (k : G P (Γ ++ I) (A :: (Δ ++ D))) (g : G P Θ (B :: Λ)) :
    G P ((Γ ++ Θ) ++ I) ((.conj A B :: (Δ ++ Λ)) ++ D) :=
  ((ExchangeScript.exchange (.conj A B :: Δ) D Λ []).reindex
    (by simp only [List.append_nil,List.cons_append,List.append_assoc])
    (by simp only [List.append_nil,List.cons_append,List.append_assoc])).right
      (((ExchangeScript.exchange Γ I Θ []).reindex
        (by simp only [List.append_nil,List.append_assoc])
        (by simp only [List.append_nil,List.append_assoc])).left (G.conjR k g))

example {P : Type u} {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (C :: Γ) (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I (C :: D)) :
    ofTerm (G.cut h (G.conjR f g)).denote =
      ofTerm (retainedFirstNative (G.cut h f) g).denote :=
  conjFirstNative_equation f g h

theorem literalChild (l : Literal Nat) : PositionalCut.Eliminated (G.identity l) (.here (.lit l) [])
    (G.identity l) (.here (.lit l) []) :=
  ⟨G.identity l,rfl,True.intro,(CutBase.identity_identity l).symm⟩

example (l : Literal Nat) : PositionalCut.Eliminated
    (G.identity l) (.here (.lit l) [])
    (G.conjR (G.identity l) (G.identity l)) (.here (.lit l) [.lit l]) :=
  CutCommutation.conjR_right_first_eliminated (G.identity l) (G.identity l)
    (G.identity l) (.here (.lit l) []) (.here (.lit l) []) rfl True.intro (literalChild l)

example : PositionalCut.Eliminated (P := Nat)
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) [])
    (G.conjR (G.identity (.neg 0)) (G.identity (.neg 0))) (.here (.lit (.neg 0)) [.lit (.neg 0)]) :=
  CutCommutation.conjR_right_first_eliminated (G.identity (.neg 0)) (G.identity (.neg 0))
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) (.here (.lit (.neg 0)) [])
    rfl True.intro (literalChild (.neg 0))

theorem emptyChild : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    G.topIdentity (.here .top []) :=
  PositionalCut.top_thin [] [] [.top] G.topI rfl True.intro

example : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    (G.conjR G.topIdentity G.topI) (.here .top []) :=
  CutCommutation.conjR_right_first_eliminated G.topIdentity G.topI G.topI
    (.here .top []) (.here .top []) rfl True.intro emptyChild

def twoTops : G Empty [.top] [.top,.top] := G.thinR [.top] [] [.top] .top G.topIdentity

theorem populatedChild : PositionalCut.Eliminated twoTops (.here .top [.top])
    G.topIdentity (.here .top []) :=
  PositionalCut.thin_thin [.top] [] [.top] [] [] [.top] .top G.topIdentity G.topI
    rfl rfl ⟨True.intro,True.intro⟩ True.intro

-- Both input exchange blocks and both output exchange blocks are nonempty.
example : PositionalCut.Eliminated twoTops (.here .top [.top])
    (G.conjR G.topIdentity twoTops) (.here .top [.top]) :=
  CutCommutation.conjR_right_first_eliminated G.topIdentity twoTops twoTops
    (.here .top [.top]) (.here .top []) rfl ⟨True.intro,⟨True.intro,True.intro⟩⟩ populatedChild

-- The original selected occurrence need not be at the child's head.
example (l : Literal Nat) :
    ofTerm (PositionalCut.cut (G.identity l) (.here (.lit l) [])
      (G.conjR (G.thinL [] [.lit l] [.lit l] .top (G.identity l)) (G.identity l))
        (.there (.here (.lit l) [.lit l]))).denote =
    ofTerm (conjRRightFirst (.there (.here (.lit l) [])) (G.identity l)
      (PositionalCut.cut (G.identity l) (.here (.lit l) [])
        (G.thinL [] [.lit l] [.lit l] .top (G.identity l)) (.there (.here (.lit l) [])))).denote := by
  simpa only [At.before,List.nil_append] using conjRRightFirst_equation
    (G.thinL [] [.lit l] [.lit l] .top (G.identity l)) (G.identity l) (G.identity l)
    (.here (.lit l) []) (.there (.here (.lit l) []))

end ConjFirstChecks

#print axioms BinaryLogical.product_left_splice

#print axioms BinaryLogical.mixed_first_residual

#print axioms BinaryLogical.conjFirstNative_equation

#print axioms BinaryLogical.conjRRightFirst_equation

#print axioms CutCommutation.conjR_right_first_rank_step
