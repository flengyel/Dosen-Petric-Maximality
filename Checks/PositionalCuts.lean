module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen

example {P : Type u} {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hf : f.CutFree) (hg : g.CutFree) :
    ∃ (f' : G P Γ Δ) (g' : G P Θ Λ),
      f'.CutFree ∧ g'.CutFree ∧ f'.Atomized ∧ g'.Atomized ∧
      AllBlockedAt f' .right x ∧ AllBlockedAt g' .left y ∧
      ofTerm f'.denote = ofTerm f.denote ∧ ofTerm g'.denote = ofTerm g.denote := by
  obtain ⟨f',g',hc,heF,heG⟩ := PositionalCut.clean_premises f x g y hf hg
  exact ⟨f',g',hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2.1,hc.2.2.2.2.2,heF,heG⟩

example {P : Type u} {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hf : f.CutFree) (hg : g.CutFree) (af : f.Atomized) (ag : g.Atomized)
    (hc : AtomicFormula C) (hr : PositionalCut.rank f x g y = 2) :
    ∃ h : G P (y.erase ++ Γ) (Λ ++ x.erase),
      h.CutFree ∧ h.Atomized ∧ ofTerm h.denote = ofTerm (PositionalCut.cut f x g y).denote :=
  PositionalCut.atomic_rank_two f x g y hf hg af ag hc hr

example {P : Type u} {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C) :
    G.cutRank (x.toHead.right f) (y.toHead.left g) =
      PositionalCut.rank f x g y + (if x.index = 0 then 0 else 1) +
        (if y.index = 0 then 0 else 1) := PositionalCut.routed_rank_eq f x g y

example {P : Type u} {F U Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (f : G P U (C :: Δ)) (g : G P (C :: Θ) Λ) :
    ofTerm (G.cut (p.left f) g).denote =
      ofTerm ((p.prefixFixed Θ).left (G.cut f g)).denote := CutCommutation.opposite_left p f g

example {P : Type u} {Γ Θ Δ F U : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) U) :
    ofTerm (G.cut f (p.right g)).denote =
      ofTerm ((p.suffixFixed Δ).right (G.cut f g)).denote := CutCommutation.opposite_right p f g

example {P : Type u} (A : NormalForm P) :
    cutDegree (.top : NormalForm P) = 1 ∧ cutDegree (.bot : NormalForm P) = 1 ∧
      cutDegree A < cutDegree (.conj A A) := ⟨rfl,rfl,cutDegree_conj_left A A⟩

#check PositionalCut.rank_two_classification
#check PositionalCut.clean_left_predecessor
#check PositionalCut.clean_right_predecessor
#check PositionalCut.rank_left_predecessor
#check PositionalCut.rank_right_predecessor
#check PositionalCut.rank_fresh_disjL
#check PositionalCut.rank_fresh_conjR
#check PositionalCut.rank_fresh_disjL_lt
#check PositionalCut.rank_fresh_conjR_lt
#check AllBlockedAt.inherit
#check allBlockedAt_iff_cluster
#check allBlockedAt_of_leaf
#check At.toHead_get_retain
#print axioms PositionalCut.atomic_rank_two
#print axioms PositionalCut.clean_premises
#print axioms PositionalCut.rank_two_classification
#print axioms CutCommutation.opposite_left
#print axioms CutCommutation.opposite_right
