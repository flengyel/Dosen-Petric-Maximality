module

public import DosenPetric.GentzenPurePortTransport
public import DosenPetric.ReducedFiniteUnion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PurePort

theorem projection_relation {A : NormalForm P} {l : Literal P} (a : PurePort .conj A l)
    (x : A.formula.Occ) (y : l.formula.Occ) : occurrenceMap a.arrow x y ↔ x = a.position := by
  induction a with
  | here l =>
    simp only [arrow,position]
    change x = y ↔ x = l.point
    rw [l.occ_unique y]
  | @left A B l a ih =>
    change occurrenceMap (comp (fst A B) a.arrow) x y ↔ x = (PurePort.left B a).position
    rw [occurrence_comp]
    simp only [position]
    change (∃ z, Relations.fstRel x z ∧ occurrenceMap a.arrow z y) ↔ x = Sum.inl a.position
    cases x <;> simp [Relations.fstRel,ih]
  | @right A B l a ih =>
    change occurrenceMap (comp (snd A B) a.arrow) x y ↔ x = (PurePort.right A a).position
    rw [occurrence_comp]
    simp only [position]
    change (∃ z, Relations.sndRel x z ∧ occurrenceMap a.arrow z y) ↔ x = Sum.inr a.position
    cases x <;> simp [Relations.sndRel,ih]

theorem injection_relation {A : NormalForm P} {l : Literal P} (a : PurePort .disj A l)
    (x : l.formula.Occ) (y : A.formula.Occ) : occurrenceMap a.arrow x y ↔ y = a.position := by
  induction a with
  | here l =>
    simp only [arrow,position]
    change x = y ↔ y = l.point
    rw [l.occ_unique x]
    exact eq_comm
  | @left A B l a ih =>
    change occurrenceMap (comp a.arrow (inl A B)) x y ↔ y = (PurePort.left B a).position
    rw [occurrence_comp]
    simp only [position]
    change (∃ z, occurrenceMap a.arrow x z ∧ Sum.inl z = y) ↔ y = Sum.inl a.position
    cases y <;> simp [ih,eq_comm]
  | @right A B l a ih =>
    change occurrenceMap (comp a.arrow (inr A B)) x y ↔ y = (PurePort.right A a).position
    rw [occurrence_comp]
    simp only [position]
    change (∃ z, occurrenceMap a.arrow x z ∧ Sum.inr z = y) ↔ y = Sum.inr a.position
    cases y <;> simp [ih,eq_comm]

end PurePort

/-- One literal edge carries both independent endpoint tags and one signed label. -/
structure PureEdge (A B : NormalForm P) where
  label : Literal P
  source : PurePort .conj A label
  target : PurePort .disj B label

namespace PureEdge
variable {A B : NormalForm P}

def arrow (e : PureEdge A B) : Hom A B := comp e.source.arrow e.target.arrow

theorem relation (e : PureEdge A B) (x : A.formula.Occ) (y : B.formula.Occ) :
    occurrenceMap e.arrow x y ↔ x = e.source.position ∧ y = e.target.position := by
  rw [arrow,occurrence_comp]
  change (∃ z, occurrenceMap e.source.arrow x z ∧ occurrenceMap e.target.arrow z y) ↔ _
  simp only [PurePort.projection_relation,PurePort.injection_relation]
  constructor
  · rintro ⟨_,hx,hy⟩; exact ⟨hx,hy⟩
  · rintro ⟨hx,hy⟩; exact ⟨e.label.point,hx,hy⟩

end PureEdge
end DosenPetric.Reduced.Gentzen
