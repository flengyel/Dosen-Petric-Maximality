module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
open DosenPetric.Reduced.Gentzen.BinaryMix

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (a : At Δ C) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (G.mix f g) (At.shift Λ a) h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank (G.mix f g) (At.shift Λ a) h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (G.mix f g) (At.shift Λ a) h z :=
  CutCommutation.mix_left_first_rank_step f g a h z hc ih

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (a : At Λ C) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (G.mix f g) (a.before Δ) h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank (G.mix f g) (a.before Δ) h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (G.mix f g) (a.before Δ) h z :=
  CutCommutation.mix_left_second_rank_step f g a h z hc ih

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (h : G P I J) (z : At J C) (a : At Γ C)
    (hc : PositionalCut.Clean h z (G.mix f g) (At.shift Θ a))
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank h z (G.mix f g) (At.shift Θ a) →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (G.mix f g) (At.shift Θ a) :=
  CutCommutation.mix_right_first_rank_step f g h z a hc ih

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (h : G P I J) (z : At J C) (a : At Θ C)
    (hc : PositionalCut.Clean h z (G.mix f g) (a.before Γ))
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank h z (G.mix f g) (a.before Γ) →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (G.mix f g) (a.before Γ) :=
  CutCommutation.mix_right_second_rank_step f g h z a hc ih

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (a : At Δ C) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (G.mix f g) (At.shift Λ a) h z).denote =
      ofTerm (firstRaw a g (PositionalCut.cut f a h z)).denote :=
  BinaryMix.first_equation f g a h z

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (a : At Δ C) (g : G P Θ Λ) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (G.mix g f) (a.before Λ) h z).denote =
      ofTerm (leadingAt a g (PositionalCut.cut f a h z)).denote :=
  BinaryMix.leadingAt_equation f a g h z

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (h : G P I J) (z : At J C) (a : At Γ C) :
    ofTerm (PositionalCut.cut h z (G.mix f g) (At.shift Θ a)).denote =
      ofTerm (rightFirstAt a g (PositionalCut.cut h z f a)).denote :=
  BinaryMix.rightFirstAt_equation f g h z a

example {P : Type u} {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (h : G P I J) (z : At J C) (a : At Θ C) :
    ofTerm (PositionalCut.cut h z (G.mix f g) (a.before Γ)).denote =
      ofTerm (secondRaw a f (PositionalCut.cut h z g a)).denote :=
  BinaryMix.second_equation f g h z a

theorem literalChild (l : Literal Nat) : PositionalCut.Eliminated (G.identity l) (.here (.lit l) [])
    (G.identity l) (.here (.lit l) []) :=
  ⟨G.identity l,rfl,True.intro,(CutBase.identity_identity l).symm⟩

-- Each test uses the actual recursive result to construct an eliminated parent.
example (l : Literal Nat) : PositionalCut.Eliminated
    (G.mix (G.identity l) (G.identity l)) (.there (.here (.lit l) []))
    (G.identity l) (.here (.lit l) []) :=
  CutCommutation.mix_left_first_eliminated (G.identity l) (G.identity l)
    (.here (.lit l) []) (G.identity l) (.here (.lit l) []) rfl (literalChild l)

example (l : Literal Nat) : PositionalCut.Eliminated
    (G.mix (G.identity l) (G.identity l)) (.here (.lit l) [.lit l])
    (G.identity l) (.here (.lit l) []) :=
  CutCommutation.mix_left_second_eliminated (G.identity l) (G.identity l)
    (.here (.lit l) []) (G.identity l) (.here (.lit l) []) rfl True.intro (literalChild l)

example (l : Literal Nat) : PositionalCut.Eliminated
    (G.identity l) (.here (.lit l) [])
    (G.mix (G.identity l) (G.identity l)) (.there (.here (.lit l) [])) :=
  CutCommutation.mix_right_first_eliminated (G.identity l) (G.identity l)
    (G.identity l) (.here (.lit l) []) (.here (.lit l) []) rfl True.intro (literalChild l)

example (l : Literal Nat) : PositionalCut.Eliminated
    (G.identity l) (.here (.lit l) [])
    (G.mix (G.identity l) (G.identity l)) (.here (.lit l) [.lit l]) :=
  CutCommutation.mix_right_second_eliminated (G.identity l) (G.identity l)
    (G.identity l) (.here (.lit l) []) (.here (.lit l) []) rfl (literalChild l)

-- No variables are required for the constant/empty-context instance.
theorem constantChild : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    G.topIdentity (.here .top []) := by
  exact PositionalCut.top_thin [] [] [.top] G.topI rfl True.intro

example : PositionalCut.Eliminated (P := Empty) (G.mix G.topI G.botE) (.here .top [])
    G.topIdentity (.here .top []) :=
  CutCommutation.mix_left_first_eliminated G.topI G.botE (.here .top [])
    G.topIdentity (.here .top []) rfl constantChild

example : PositionalCut.Eliminated (P := Empty) G.topI (.here .top [])
    (G.mix G.topIdentity G.botE) (.there (.here .top [])) :=
  CutCommutation.mix_right_first_eliminated G.topIdentity G.botE G.topI
    (.here .top []) (.here .top []) rfl True.intro constantChild

example : PositionalCut.Eliminated (P := Nat)
    (G.mix (G.identity (.neg 0)) (G.identity (.neg 0))) (.there (.here (.lit (.neg 0)) []))
    (G.identity (.neg 0)) (.here (.lit (.neg 0)) []) :=
  CutCommutation.mix_left_first_eliminated _ _ _ _ _ rfl (literalChild (.neg 0))

#print axioms CutCommutation.mix_left_first_rank_step

#print axioms CutCommutation.mix_left_second_rank_step

#print axioms CutCommutation.mix_right_first_rank_step

#print axioms CutCommutation.mix_right_second_rank_step
