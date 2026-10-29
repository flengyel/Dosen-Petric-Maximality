module

public import DosenPetric.ManuscriptFinalConsequences

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation.ManuscriptSubstitution
universe u
variable {P : Type u}

/-- The manuscript's substitution fixes every variable other than p. Decidable
variable equality is chosen internally and is not a theorem hypothesis. -/
noncomputable def replace (p : P) (A : Formula P) : P → Formula P := by
  classical
  exact fun q => if q=p then A else .var q

theorem replace_at (p : P) (A : Formula P) : replace p A p = A := by
  classical
  simp only [replace,ite_true]

theorem replace_other (p q : P) (A : Formula P) (h : q ≠ p) : replace p A q = .var q := by
  classical
  simp only [replace,ite_eq_right h]

theorem positive_single_context (p : P) (A : Formula P) :
    HEq (substitute (replace p A) (context (.var p))) (context A) := by
  change HEq (context (replace p A p)) (context A)
  rw [replace_at]

theorem negative_single_context (p : P) (A : Formula P) :
    HEq (substitute (replace p (.neg A)) (context (.neg (.var p)) )) (context (.neg (.neg A))) := by
  change HEq (context (.neg (replace p (.neg A) p))) (context (.neg (.neg A)))
  rw [replace_at]

end DosenPetric.Presentation.ManuscriptSubstitution
