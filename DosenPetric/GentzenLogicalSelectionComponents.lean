module

public import DosenPetric.GentzenMixedSelectionComponents

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.Route
universe u
variable {P : Type u} {F K U L : List (NormalForm P)}
variable (p : Route K F) (q : Route L U)

/-- Conjunction-right is natural in its two antecedent context routes. -/
theorem parallel_conjRight {Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : Term P (ante F) (succ (A::Δ))) (g : Term P (ante U) (succ (B::Λ))) :
    comp (ofTerm (p.parallel q).product) (ofTerm (Rules.conjRight f g)) =
      ofTerm (Rules.conjRight (.comp p.product f) (.comp q.product g)) := by
  have h := parallel_split .conj p q
  change comp (ofTerm (p.parallel q).product) (ofTerm (Gentzen.append .conj F U).invTerm) =
    comp (ofTerm (Gentzen.append .conj K L).invTerm)
      (tensor .conj (ofTerm p.product) (ofTerm q.product)) at h
  simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor]
  rw [←Laws.assoc,h,Laws.assoc,←Laws.assoc (tensor .conj _ _),Laws.tensor_comp]

/-- Disjunction-left is natural in its two succedent context routes. -/
theorem parallel_disjLeft {Γ Θ : List (NormalForm P)} {A B : NormalForm P}
    (f : Term P (ante (A::Γ)) (succ F)) (g : Term P (ante (B::Θ)) (succ U)) :
    comp (ofTerm (Rules.disjLeft f g)) (ofTerm (p.parallel q).coproduct) =
      ofTerm (Rules.disjLeft (.comp f p.coproduct) (.comp g q.coproduct)) := by
  have h := parallel_split .disj p q
  change comp (ofTerm (Gentzen.append .disj F U).toTerm) (ofTerm (p.parallel q).coproduct) =
    comp (tensor .disj (ofTerm p.coproduct) (ofTerm q.coproduct))
      (ofTerm (Gentzen.append .disj K L).toTerm) at h
  simp only [Rules.disjLeft,ofTerm_comp,ofTerm_tensor]
  rw [Laws.assoc,Laws.assoc,Laws.assoc,Laws.assoc,Laws.assoc,h,
    ←Laws.assoc (tensor .disj _ _),Laws.tensor_comp]
  simp only [←Laws.tensor_comp,Laws.assoc]

end DosenPetric.Reduced.Gentzen.Route
