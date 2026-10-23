module

public import DosenPetric.PositiveGentzenization

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- The original tagged position, in the non-unit branch of a singleton fold. -/
def singletonOcc (o : Op) (A : NormalForm P) (x : A.formula.Occ) :
    (fold o [A]).formula.Occ := by cases o <;> exact Sum.inl x

def singletonFrom (o : Op) (A : NormalForm P) :
    (fold o [A]).formula.Occ → A.formula.Occ := by
  cases o <;> exact fun x => match x with | .inl a => a | .inr e => nomatch e

theorem singletonFrom_to (o : Op) (A : NormalForm P) (x : A.formula.Occ) :
    singletonFrom o A (singletonOcc o A x) = x := by cases o <;> rfl

theorem singletonOcc_from (o : Op) (A : NormalForm P) (x : (fold o [A]).formula.Occ) :
    singletonOcc o A (singletonFrom o A x) = x := by
  cases o <;> cases x with
  | inl x => rfl
  | inr e => cases e

theorem singletonOcc_injective (o : Op) (A : NormalForm P) {x y : A.formula.Occ}
    (h : singletonOcc o A x = singletonOcc o A y) : x = y :=
  (singletonFrom_to o A x).symm.trans
    ((congrArg (singletonFrom o A) h).trans (singletonFrom_to o A y))

theorem encode_relation {A B : NormalForm P} (t : Term P A B)
    (x : A.formula.Occ) (y : B.formula.Occ) :
    (encode t).relation (singletonOcc .conj A x) (singletonOcc .disj B y) ↔ t.relation x y := by
  simp [encode, Term.relation, Relations.comp, Relations.graph, singletonOcc,
    Presentation.Occurrence.dropRight]

/-- Gentzenization preserves the entire original tagged relation in singleton coordinates. -/
theorem gentzenization_occurrences {A B : NormalForm P} (t : Term P A B) (h : t.Positive) :
    ∃ g : G P [A] [B],
      ofTerm g.denote = comp (rightOut .conj A) (comp (ofTerm t) (rightIn .disj B)) ∧
      ∀ (x : A.formula.Occ) (y : B.formula.Occ),
        g.relation (singletonOcc .conj A x) (singletonOcc .disj B y) ↔ t.relation x y := by
  obtain ⟨g, hg⟩ := gentzenization t h
  refine ⟨g, hg, ?_⟩
  intro x y
  have hmap := congrArg (fun f => occurrenceMap f
    (singletonOcc .conj A x) (singletonOcc .disj B y)) hg
  change g.relation _ _ = (encode t).relation _ _ at hmap
  exact (Iff.of_eq hmap).trans (encode_relation t x y)

end DosenPetric.Reduced.Gentzen
