module

public import DosenPetric.GentzenPrincipalDisjunctionSelected
public import DosenPetric.GentzenPrincipalConjunctionSelected

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- The outer induction hypothesis, restricted strictly below the current degree. -/
def DegreeBelow (P : Type u) (n : Nat) : Prop :=
  ∀ (C : NormalForm P), cutDegree C < n →
    ∀ {Γ Δ Θ Λ : List (NormalForm P)} (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ),
      f.CutFree → g.CutFree →
      ∃ h : G P (Θ ++ Γ) (Λ ++ Δ),
        h.CutFree ∧ h.Atomized ∧ ofTerm h.denote = ofTerm (G.cut f g).denote

namespace PrincipalConjunction
variable {Γ Θ Δ Λ F U V : List (NormalForm P)} {A B : NormalForm P}

/-- The conjunction principal branch of the degree induction, with the inner cut eliminated first. -/
theorem degree_step (ih : DegreeBelow P (cutDegree (.conj A B)))
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P (F ++ A :: B :: U) V)
    (hf : f.CutFree) (hg : g.CutFree) (hh : h.CutFree) :
    PositionalCut.Eliminated (G.conjR f g) (.here (.conj A B) (Δ ++ Λ))
      (G.conjL F U V A B h) (At.shift F (.here (.conj A B) U)) := by
  let h' := (LogicalHeadRouting.components F U A B (.conj A B)).left h
  have hh' : h'.CutFree := by
    change h'.cutCount = 0
    rw [ExchangeScript.left_count]
    exact hh
  obtain ⟨a,ha,aa,ea⟩ := ih A (cutDegree_conj_left A B) f h' hf hh'
  obtain ⟨b,hb,ab,eb⟩ := ih B (cutDegree_conj_right A B) g a hg ha
  let p := ExchangeScript.appendAssoc (At.shift F (.here (.conj A B) U)).erase Γ Θ
  let q := ExchangeScript.appendAssoc V Δ Λ
  refine ⟨q.right (p.left b), ?_, ?_, ?_⟩
  · change (q.right (p.left b)).cutCount = 0
    rw [ExchangeScript.right_count, ExchangeScript.left_count]
    exact hb
  · exact (q.right_atomized _).mpr ((p.left_atomized _).mpr ab)
  · have e : ofTerm b.denote = ofTerm (G.cut g (G.cut f h')).denote :=
      eb.trans (Rules.cut_congr rfl ea)
    have er := congrArg (fun k => comp (comp (p.arrow .conj) k) (q.arrow .disj)) e
    have ew : ofTerm (q.right (p.left b)).denote = ofTerm (selectedReduction f g h).denote := by
      simpa only [ExchangeScript.right_denote, ExchangeScript.left_denote,
        selectedReduction, reduction, p, q, h'] using er
    exact ew.trans (selected_equation f g h).symm

end PrincipalConjunction
namespace PrincipalDisjunction
variable {Γ Θ Ξ F U Λ Ω : List (NormalForm P)} {A B : NormalForm P}

/-- The disjunction principal branch uses no bound on the returned smaller-degree proof ranks. -/
theorem degree_step (ih : DegreeBelow P (cutDegree (.disj A B)))
    (f : G P Γ (F ++ A :: B :: U)) (g : G P (A :: Θ) Λ) (h : G P (B :: Ξ) Ω)
    (hf : f.CutFree) (hg : g.CutFree) (hh : h.CutFree) :
    PositionalCut.Eliminated (G.disjR Γ F U A B f) (At.shift F (.here (.disj A B) U))
      (G.disjL g h) (.here (.disj A B) (Θ ++ Ξ)) := by
  let f' := (LogicalHeadRouting.components F U A B (.disj A B)).right f
  let d := (At.shift F (.here (.disj A B) U)).erase
  let r := HeadRouting.front [A] d B
  have hf' : (r.right f').CutFree := by
    change (r.right f').cutCount = 0
    rw [ExchangeScript.right_count, ExchangeScript.right_count]
    exact hf
  obtain ⟨a,ha,aa,ea⟩ := ih B (cutDegree_disj_right A B) (r.right f') h hf' hh
  let s := HeadRouting.front Ω d A
  have has : (s.right a).CutFree := by
    change (s.right a).cutCount = 0
    rw [ExchangeScript.right_count]
    exact ha
  obtain ⟨b,hb,ab,eb⟩ := ih A (cutDegree_disj_left A B) (s.right a) g has hg
  let p := (ExchangeScript.appendAssoc Θ Ξ Γ).inverse
  let q := (ExchangeScript.appendAssoc Λ Ω d).inverse
  refine ⟨q.right (p.left b), ?_, ?_, ?_⟩
  · change (q.right (p.left b)).cutCount = 0
    rw [ExchangeScript.right_count, ExchangeScript.left_count]
    exact hb
  · exact (q.right_atomized _).mpr ((p.left_atomized _).mpr ab)
  · have es : ofTerm (s.right a).denote = ofTerm (s.right (G.cut (r.right f') h)).denote := by
      simpa only [ExchangeScript.right_denote] using
        congrArg (fun k => comp k (s.arrow .disj)) ea
    have e : ofTerm b.denote = ofTerm (G.cut (s.right (G.cut (r.right f') h)) g).denote :=
      eb.trans (Rules.cut_congr es rfl)
    have er := congrArg (fun k => comp (comp (p.arrow .conj) k) (q.arrow .disj)) e
    have ew : ofTerm (q.right (p.left b)).denote = ofTerm (selectedReduction f g h).denote := by
      simpa only [ExchangeScript.right_denote, ExchangeScript.left_denote,
        selectedReduction, reduction, p, q, r, s, f', d] using er
    exact ew.trans (selected_equation f g h).symm

end PrincipalDisjunction
end DosenPetric.Reduced.Gentzen
