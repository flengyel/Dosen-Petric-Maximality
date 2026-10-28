module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen

example {P : Type u} {F U Δ Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (F ++ A :: B :: U) Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C) :
    ofTerm (PositionalCut.cut (G.conjL F U Δ A B f) x g y).denote =
      ofTerm (PrefixedLogical.conjL y.erase F U (Λ ++ x.erase) A B
        (PositionalCut.cut f x g y)).denote := CutCommutation.opposite_conjL f x g y

example {P : Type u} {Γ Δ Θ F U : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ (F ++ A :: B :: U)) (y : At Θ C) :
    ofTerm (PositionalCut.cut f x (G.disjR Θ F U A B g) y).denote =
      ofTerm (SuffixedLogical.disjR (y.erase ++ Γ) F U x.erase A B
        (PositionalCut.cut f x g y)).denote := CutCommutation.opposite_disjR f x g y

example {P : Type u} {F U Δ Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (F ++ A :: B :: U) Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hc : PositionalCut.Clean (G.conjL F U Δ A B f) x g y) :
    PositionalCut.Clean f x g y ∧
      PositionalCut.rank f x g y < PositionalCut.rank (G.conjL F U Δ A B f) x g y :=
  PositionalCut.opposite_conjL_descent f x g y hc

example {P : Type u} {Γ Δ Θ F U : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ (F ++ A :: B :: U)) (y : At Θ C)
    (hc : PositionalCut.Clean f x (G.disjR Θ F U A B g) y) :
    PositionalCut.Clean f x g y ∧
      PositionalCut.rank f x g y < PositionalCut.rank f x (G.disjR Θ F U A B g) y :=
  PositionalCut.opposite_disjR_descent f x g y hc

example {P : Type u} (o : Op) (K : List (NormalForm P)) {U V : List (NormalForm P)}
    (r : (side P o).Hom (fold o U) (fold o V)) :
    (side P o).comp (prefixSide o K r) (split o K V) =
      (side P o).comp (split o K U) ((sideM P o).tensor ((side P o).id (fold o K)) r) :=
  prefixSide_split o K r

example {P : Type u} (o : Op) (F U K : List (NormalForm P)) (A : NormalForm P) :
    (side P o).comp (suffixLogicalSide o F U K A A) (split o (F ++ A :: A :: U) K) =
      (side P o).comp (split o (F ++ o.formula A A :: U) K)
        ((sideM P o).tensor (logicalSide o F U A A) ((side P o).id (fold o K))) :=
  suffixLogicalSide_split o F U K A A

example (f : G Empty [.top,.bot] [.top]) (g : G Empty [.top] [.top]) :
    ofTerm (PositionalCut.cut (G.conjL [] [] [.top] .top .bot f) (.here .top [])
      g (.here .top [])).denote =
      ofTerm (PrefixedLogical.conjL [] [] [] [.top] .top .bot
        (PositionalCut.cut f (.here .top []) g (.here .top []))).denote :=
  CutCommutation.opposite_conjL (F := []) (U := []) (A := .top) (B := .bot)
    f (.here .top []) g (.here .top [])

#check CutCommutation.opposite_conjL_rank_step
#check CutCommutation.opposite_disjR_rank_step
#print axioms CutCommutation.opposite_conjL
#print axioms CutCommutation.opposite_disjR
#print axioms CutCommutation.opposite_conjL_rank_step
#print axioms CutCommutation.opposite_disjR_rank_step
#print axioms suffixLogicalSide_split
