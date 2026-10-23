module

public import DosenPetric.ReducedUnion

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}

namespace Term

/-- Tagged relation union, without identifying positions having equal labels. -/
theorem relation_union {A B : NormalForm P} (f g : Term P A B)
    (x : A.formula.Occ) (y : B.formula.Occ) :
    (f.union g).relation x y ↔ f.relation x y ∨ g.relation x y := by
  simp [union, relation, Relations.comp, Relations.pair, Relations.copair,
    Relations.sumMap, Relations.graph, Sum.exists]

theorem relation_zeroOf {A B : NormalForm P} (f : Term P A B) :
    f.zeroOf.relation = Relations.empty := Relations.empty_comp f.relation

end Term

theorem occurrence_union {A B : NormalForm P} (f g : Hom A B)
    (x : A.formula.Occ) (y : B.formula.Occ) :
    occurrenceMap (union f g) x y ↔ occurrenceMap f x y ∨ occurrenceMap g x y := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g =>
  exact f.relation_union g x y

theorem occurrence_zero (A : NormalForm P) : occurrenceMap (zero A) = Relations.empty := rfl

theorem occurrence_zeroOf {A B : NormalForm P} (f : Hom A B) :
    occurrenceMap (zeroOf f) = Relations.empty := by
  rw [zeroOf, occurrence_comp, occurrence_zero, Relations.empty_comp]

end DosenPetric.Reduced
