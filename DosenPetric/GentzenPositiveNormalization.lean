module

public import DosenPetric.GentzenCutElimination
public import DosenPetric.GentzenOccurrences

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Positive arrows have cut-free atomized Gentzen representatives with the
complete original tagged relation, including the empty occurrence cases. -/
theorem positive_cutFree_represented {A B : NormalForm P} (t : Term P A B)
    (ht : t.Positive) :
    ∃ g : G P [A] [B], g.CutFree ∧ g.Atomized ∧
      ofTerm g.denote = comp (rightOut .conj A) (comp (ofTerm t) (rightIn .disj B)) ∧
      ∀ (x : A.formula.Occ) (y : B.formula.Occ),
        g.relation (singletonOcc .conj A x) (singletonOcc .disj B y) ↔ t.relation x y := by
  obtain ⟨g,eg,rg⟩ := gentzenization_occurrences t ht
  obtain ⟨h,hh,ah,eh⟩ := atomized_cut_elimination g
  refine ⟨h,hh,ah,eh.trans eg,?_⟩
  intro x y
  have he := congrArg (fun f => occurrenceMap f
    (singletonOcc .conj A x) (singletonOcc .disj B y)) eh
  change h.relation _ _ = g.relation _ _ at he
  exact (Iff.of_eq he).trans (rg x y)

/-- Decoding the same cut-free atomized witness recovers the original arrow. -/
theorem positive_cutFree_decode {A B : NormalForm P} (t : Term P A B)
    (ht : t.Positive) :
    ∃ g : G P [A] [B], g.CutFree ∧ g.Atomized ∧ decode g.denote = ofTerm t := by
  obtain ⟨g,eg⟩ := gentzenization_decode t ht
  obtain ⟨h,hh,ah,eh⟩ := atomized_cut_elimination g
  refine ⟨h,hh,ah,?_⟩
  change comp (rightIn .conj A) (comp (ofTerm h.denote) (rightOut .disj B)) = _
  rw [eh]
  exact eg

end DosenPetric.Reduced.Gentzen
