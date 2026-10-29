module
import DosenPetric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
open PositionalCut
namespace GlobalCutEliminationChecks
example {P : Type u} : CutElimination P := cut_elimination
example {P : Type u} : AtomizedCutElimination P := atomized_cut_elimination
example {P : Type u} {Γ Δ : List (NormalForm P)} (t : G P Γ Δ) :
    ∃ h : G P Γ Δ, h.CutFree ∧ h.Atomized ∧ ofTerm h.denote = ofTerm t.denote :=
  atomized_cut_elimination t

example {P : Type u} {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hb : BlockedR f) (hx : f.LowerContraction .right x) (hc : PositionalCut.Clean f x g y)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C), PositionalCut.rank b v d w < PositionalCut.rank f x g y →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated f x g y :=
  CutCommutation.blocked_right_rank_step f x g y hb hx hc ih

example {P : Type u} {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (h : G P Γ Δ) (z : At Δ C) (g : G P Θ Λ) (x : At Θ C)
    (hb : BlockedL g) (hx : g.LowerContraction .left x) (hc : PositionalCut.Clean h z g x)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C), PositionalCut.rank b v d w < PositionalCut.rank h z g x →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z g x :=
  CutCommutation.blocked_left_rank_step h z g x hb hx hc ih

example {P : Type u} {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hp : f.Parametric .right x) (hc : PositionalCut.Clean f x g y)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C), PositionalCut.rank b v d w < PositionalCut.rank f x g y →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated f x g y :=
  CutCommutation.parametric_right_rank_step f x g y hp hc ih

example {P : Type u} {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (h : G P Γ Δ) (z : At Δ C) (g : G P Θ Λ) (x : At Θ C)
    (hp : g.Parametric .left x) (hc : PositionalCut.Clean h z g x)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C), PositionalCut.rank b v d w < PositionalCut.rank h z g x →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z g x :=
  CutCommutation.parametric_left_rank_step h z g x hp hc ih

example {P : Type u} {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (hd : DegreeBelow P (cutDegree C))
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hc : Clean f x g y)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C), rank b v d w < rank f x g y →
      Clean b v d w → Eliminated b v d w) : Eliminated f x g y :=
  PositionalCut.clean_rank_step hd f x g y hc ih

example {P : Type u} {C : NormalForm P} (hd : DegreeBelow P (cutDegree C))
    {Γ Δ Θ Λ : List (NormalForm P)}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hc : Clean f x g y) : Eliminated f x g y :=
  PositionalCut.clean_elimination hd f x g y hc

example {P : Type u} {C : NormalForm P} (hd : DegreeBelow P (cutDegree C))
    {Γ Δ Θ Λ : List (NormalForm P)}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hf : f.CutFree) (hg : g.CutFree) : Eliminated f x g y :=
  PositionalCut.cutFree_degree_step hd f x g y hf hg

example {P : Type u} (C : NormalForm P)
    {Γ Δ Θ Λ : List (NormalForm P)} (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ)
    (hf : f.CutFree) (hg : g.CutFree) :
    ∃ h : G P (Θ ++ Γ) (Λ ++ Δ),
      h.CutFree ∧ h.Atomized ∧ ofTerm h.denote = ofTerm (G.cut f g).denote :=
  head_cut_elimination C f g hf hg

example {P : Type u} {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hf : f.CutFree) (hg : g.CutFree) : Eliminated f x g y :=
  PositionalCut.cutFree_elimination f x g y hf hg

/-- These witnesses use the actual global eliminator, including a cut below thinning. -/
example {P : Type u} (l : Literal P) :
    ∃ h : G P [.lit l] [.lit l], h.CutFree ∧ h.Atomized ∧
      ofTerm h.denote = ofTerm (G.cut (G.identity l) (G.zero l)).denote :=
  atomized_cut_elimination (G.cut (G.identity l) (G.zero l))
example : ∃ h : G Empty [.bot] [.top,.top], h.CutFree ∧ h.Atomized ∧
    ofTerm h.denote = ofTerm (G.thinR [.bot] [] [.top] .top
      (G.cut (G.thinR [.bot] [] [] .top G.botE) (G.identityNF .top))).denote :=
  atomized_cut_elimination _
example : ∃ h : G Nat [.lit (.neg 0)] [.conj (.lit (.neg 0)) .top],
    h.CutFree ∧ h.Atomized ∧ ofTerm h.denote = ofTerm
      (G.cut (G.conjR (G.identity (.neg 0)) G.topI)
        (G.identityNF (.conj (.lit (.neg 0)) .top))).denote :=
  atomized_cut_elimination _
example {P : Type u} {Γ Δ : List (NormalForm P)} (t : G P Γ Δ) :
    ∃ h : G P (Γ++Γ) (Δ++Δ), h.CutFree ∧ h.Atomized ∧
      ofTerm h.denote = ofTerm (G.mix t t).denote := atomized_cut_elimination _
example : cutDegree (.top : NormalForm Empty) = 1 := rfl
example : cutDegree (.bot : NormalForm Empty) = 1 := rfl
example (l : Literal Nat) : cutDegree (.lit l) = 0 := rfl
end GlobalCutEliminationChecks

#print axioms DosenPetric.Reduced.Gentzen.CutCommutation.blocked_right_rank_step

#print axioms DosenPetric.Reduced.Gentzen.CutCommutation.blocked_left_rank_step

#print axioms DosenPetric.Reduced.Gentzen.CutCommutation.parametric_right_rank_step

#print axioms DosenPetric.Reduced.Gentzen.CutCommutation.parametric_left_rank_step

#print axioms DosenPetric.Reduced.Gentzen.PositionalCut.clean_rank_step

#print axioms DosenPetric.Reduced.Gentzen.PositionalCut.clean_elimination

#print axioms DosenPetric.Reduced.Gentzen.PositionalCut.cutFree_degree_step

#print axioms DosenPetric.Reduced.Gentzen.head_cut_elimination

#print axioms DosenPetric.Reduced.Gentzen.PositionalCut.cutFree_elimination

#print axioms DosenPetric.Reduced.Gentzen.G.cut_free_normalization

#print axioms DosenPetric.Reduced.Gentzen.cut_elimination

#print axioms DosenPetric.Reduced.Gentzen.atomized_cut_elimination
