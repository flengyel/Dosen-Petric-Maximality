module

public import DosenPetric.GentzenSelectedBlocked

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Formula degree for the outer cut induction; the two constants have degree one. -/
def cutDegree : NormalForm P → Nat
  | .lit _ => 0
  | .top | .bot => 1
  | .conj A B | .disj A B => 1 + cutDegree A + cutDegree B

theorem cutDegree_conj_left (A B : NormalForm P) : cutDegree A < cutDegree (.conj A B) := by
  simp only [cutDegree]; omega

theorem cutDegree_conj_right (A B : NormalForm P) : cutDegree B < cutDegree (.conj A B) := by
  simp only [cutDegree]; omega

theorem cutDegree_disj_left (A B : NormalForm P) : cutDegree A < cutDegree (.disj A B) := by
  simp only [cutDegree]; omega

theorem cutDegree_disj_right (A B : NormalForm P) : cutDegree B < cutDegree (.disj A B) := by
  simp only [cutDegree]; omega

/-- The same-sequent endpoint, with no hypothesis on the input proof. -/
def CutElimination (P : Type u) : Prop :=
  ∀ {Γ Δ : List (NormalForm P)} (t : G P Γ Δ),
    ∃ t' : G P Γ Δ, t'.CutFree ∧ ofTerm t'.denote = ofTerm t.denote

/-- The endpoint with both cut elimination and thinning atomization. -/
def AtomizedCutElimination (P : Type u) : Prop :=
  ∀ {Γ Δ : List (NormalForm P)} (t : G P Γ Δ),
    ∃ t' : G P Γ Δ, t'.CutFree ∧ t'.Atomized ∧ ofTerm t'.denote = ofTerm t.denote

end DosenPetric.Reduced.Gentzen
