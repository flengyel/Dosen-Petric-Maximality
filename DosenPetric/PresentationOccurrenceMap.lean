module

public import DosenPetric.PresentationOccurrences

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.Presentation

universe u

variable {P : Type u}

attribute [local simp] Term.relation Term.medial Term.distRight Relations.comp Relations.graph
  Relations.sumMap Relations.pair Relations.copair Relations.fstRel Relations.sndRel
  Relations.reassoc Relations.empty Occurrence.unassoc Occurrence.exchange
  Occurrence.dropRight Occurrence.dropLeft Sum.exists
  Occurrence.sumMap_graph Relations.graph_comp Relations.id_comp Relations.comp_id
  Relations.empty_comp Relations.comp_empty Sum.map

/-- Every derivation preserves the relation, separately from any converse. -/
theorem Derives.relation {A B : Formula P} {f g : Term P A B} (e : Derives f g) :
    f.relation = g.relation := by
  induction e with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | comp _ _ ih ih' => exact (congrArg (fun r => Relations.comp r _) ih).trans (congrArg (Relations.comp _) ih')
  | tensor o _ _ ih ih' => cases o <;> exact (congrArg (fun r => Relations.sumMap r _) ih).trans (congrArg (Relations.sumMap _) ih')
  | equation e => exact e.relation

/-- The well-defined covariant occurrence assignment on the source quotient. -/
def occurrenceMap {A B : Formula P} (f : Hom A B) : Relations.Rel A.Occ B.Occ :=
  Quotient.liftOn f Term.relation (fun _ _ h => h.relation)

theorem ofTerm_eq_iff {A B : Formula P} (f g : Term P A B) :
    ofTerm f = ofTerm g ↔ Derives f g := ⟨Quotient.exact, sound⟩

theorem occurrence_ofTerm {A B : Formula P} (t : Term P A B) :
    occurrenceMap (ofTerm t) = t.relation := rfl

theorem occurrence_diag (A : Formula P) : occurrenceMap (diag A) =
    Relations.pair (Relations.graph _root_.id) (Relations.graph _root_.id) := rfl

theorem occurrence_codiag (A : Formula P) : occurrenceMap (codiag A) =
    Relations.copair (Relations.graph _root_.id) (Relations.graph _root_.id) := rfl

theorem occurrence_id (A : Formula P) : occurrenceMap (id A) = Relations.graph _root_.id := rfl

theorem occurrence_comp {A B C : Formula P} (f : Hom A B) (g : Hom B C) :
    occurrenceMap (comp f g) = Relations.comp (occurrenceMap f) (occurrenceMap g) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

theorem occurrence_tensor_conj {A B C D : Formula P} (f : Hom A C) (g : Hom B D) :
    occurrenceMap (tensor .conj f g) = Relations.sumMap (occurrenceMap f) (occurrenceMap g) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

theorem occurrence_tensor_disj {A B C D : Formula P} (f : Hom A C) (g : Hom B D) :
    occurrenceMap (tensor .disj f g) = Relations.sumMap (occurrenceMap f) (occurrenceMap g) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

theorem occurrence_fst (A B : Formula P) : occurrenceMap (fst A B) = Relations.fstRel := rfl
theorem occurrence_snd (A B : Formula P) : occurrenceMap (snd A B) = Relations.sndRel := rfl
theorem occurrence_inl (A B : Formula P) : occurrenceMap (inl A B) = Relations.graph Sum.inl := rfl
theorem occurrence_inr (A B : Formula P) : occurrenceMap (inr A B) = Relations.graph Sum.inr := rfl

theorem occurrence_pair {X A B : Formula P} (f : Hom X A) (g : Hom X B) :
    occurrenceMap (pair f g) = Relations.pair (occurrenceMap f) (occurrenceMap g) := by
  rw [pair, occurrence_comp, occurrence_tensor_conj, occurrence_diag]
  funext x y
  apply propext
  cases y <;> simp

theorem occurrence_copair {A B X : Formula P} (f : Hom A X) (g : Hom B X) :
    occurrenceMap (copair f g) = Relations.copair (occurrenceMap f) (occurrenceMap g) := by
  rw [copair, occurrence_comp, occurrence_tensor_disj, occurrence_codiag]
  funext x y
  apply propext
  cases x <;> simp

theorem occurrence_toTop (A : Formula P) : occurrenceMap (toTop A) = Relations.empty := by
  funext x y
  exact Empty.elim y

theorem occurrence_fromBot (A : Formula P) : occurrenceMap (fromBot A) = Relations.empty := by
  funext x y
  exact Empty.elim x

theorem occurrence_dist (A B C : Formula P) :
    occurrenceMap (dist A B C) = Relations.graph Relations.reassoc := rfl

theorem occurrence_distRight (A B C : Formula P) :
    occurrenceMap (distRight A B C) = Relations.graph Occurrence.unassoc :=
  Term.relation_distRight A B C

theorem occurrence_zero (A : Formula P) : occurrenceMap (zeroConstruction A) = Relations.empty := by
  rw [zeroConstruction_eq]
  rfl

theorem occurrence_excludedMiddle (A : Formula P) :
    occurrenceMap (excludedMiddle A) = Relations.empty := rfl

theorem occurrence_contradiction (A : Formula P) :
    occurrenceMap (contradiction A) = Relations.empty := rfl

/-- A concrete failure of thinness in the original syntactic quotient. -/
theorem nonthin (p : P) : fst (.var p) (.var p) ≠ snd (.var p) (.var p) := by
  intro h
  have hr := congrArg occurrenceMap h
  exact Relations.projections_distinct hr

end DosenPetric.Presentation
