module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
open DosenPetric.Reduced.Gentzen.BinaryLogical

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I J) (z : At J C) (a : At Θ C) :
    ofTerm (PositionalCut.cut h z (G.conjR f g) (At.shift Γ a)).denote =
      ofTerm (conjRRightSecond f a (PositionalCut.cut h z g a)).denote :=
  BinaryLogical.conjRRightSecond_equation f g h z a

example {P : Type u} {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (a : At Θ C) (k : G P (a.erase ++ I) ((B :: Λ) ++ D)) :
    (conjRRightSecond f a k).cutCount = f.cutCount + k.cutCount :=
  BinaryLogical.conjRRightSecond_count f a k

example {P : Type u} {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (a : At Θ C) (k : G P (a.erase ++ I) ((B :: Λ) ++ D)) :
    (conjRRightSecond f a k).Atomized ↔ f.Atomized ∧ k.Atomized :=
  BinaryLogical.conjRRightSecond_atomized f a k

example {P : Type u} {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (a : At Θ C) (k k' : G P (a.erase ++ I) ((B :: Λ) ++ D))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (conjRRightSecond f a k).denote = ofTerm (conjRRightSecond f a k').denote :=
  BinaryLogical.conjRRightSecond_congr f a k k' hk

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I J) (z : At J C) (a : At Θ C)
    (hc : PositionalCut.Clean h z (G.conjR f g) (At.shift Γ a))
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank h z (G.conjR f g) (At.shift Γ a) →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (G.conjR f g) (At.shift Γ a) :=
  CutCommutation.conjR_right_second_rank_step f g h z a hc ih

theorem literalChild (l : Literal Nat) : PositionalCut.Eliminated (G.identity l) (.here (.lit l) [])
    (G.identity l) (.here (.lit l) []) :=
  ⟨G.identity l,rfl,True.intro,(CutBase.identity_identity l).symm⟩

-- Equal formula labels occupy two distinct inputs in this actual reconstruction.
example (l : Literal Nat) : PositionalCut.Eliminated
    (G.identity l) (.here (.lit l) [])
    (G.conjR (G.identity l) (G.identity l)) (.there (.here (.lit l) [])) :=
  CutCommutation.conjR_right_second_eliminated _ _ _ _ _ rfl True.intro (literalChild l)

example : PositionalCut.Eliminated (P := Nat)
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) [])
    (G.conjR (G.identity (.neg 0)) (G.identity (.neg 0))) (.there (.here (.lit (.neg 0)) [])) :=
  CutCommutation.conjR_right_second_eliminated _ _ _ _ _ rfl True.intro (literalChild (.neg 0))

theorem constantChild : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    G.topIdentity (.here .top []) :=
  PositionalCut.top_thin [] [] [.top] G.topI rfl True.intro

example : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    (G.conjR G.topI G.topIdentity) (.here .top []) :=
  CutCommutation.conjR_right_second_eliminated _ _ _ _ _ rfl True.intro constantChild

#print axioms CutCommutation.conjR_right_second_rank_step

#print axioms BinaryLogical.conjRRightSecond_equation

#print axioms BinaryLogical.mixedDisj_swap
