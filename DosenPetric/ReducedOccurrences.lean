module

public import DosenPetric.SignedLiteralReduction

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.Reduced

universe u

namespace Term

open Relations Presentation.Occurrence

def relation {P : Type u} : {A B : NormalForm P} → Term P A B → Rel A.formula.Occ B.formula.Occ
  | _, _, .id A => graph _root_.id
  | _, _, .comp f g => Relations.comp (relation f) (relation g)
  | _, _, .tensor .conj f g => sumMap (relation f) (relation g)
  | _, _, .tensor .disj f g => sumMap (relation f) (relation g)
  | _, _, .assocR .conj A B C => graph reassoc
  | _, _, .assocR .disj A B C => graph reassoc
  | _, _, .assocL .conj A B C => graph unassoc
  | _, _, .assocL .disj A B C => graph unassoc
  | _, _, .swap .conj A B => graph exchange
  | _, _, .swap .disj A B => graph exchange
  | _, _, .diag A => Relations.pair (graph _root_.id) (graph _root_.id)
  | _, _, .codiag A => Relations.copair (graph _root_.id) (graph _root_.id)
  | _, _, .fst A B => fstRel
  | _, _, .snd A B => sndRel
  | _, _, .inl A B => graph Sum.inl
  | _, _, .inr A B => graph Sum.inr
  | _, _, .rightOut .conj A => graph dropRight
  | _, _, .rightOut .disj A => graph dropRight
  | _, _, .rightIn .conj A => graph Sum.inl
  | _, _, .rightIn .disj A => graph Sum.inl
  | _, _, .leftOut .conj A => graph dropLeft
  | _, _, .leftOut .disj A => graph dropLeft
  | _, _, .leftIn .conj A => graph Sum.inr
  | _, _, .leftIn .disj A => graph Sum.inr
  | _, _, .mix A B => graph _root_.id
  | _, _, .dist A B C => graph reassoc
  | _, _, .zero A => empty
  | _, _, .eta p => empty
  | _, _, .epsilon p => empty

variable {P : Type u}

theorem relation_toFull {A B : NormalForm P} (t : Term P A B) :
    t.relation = t.toFull.relation := by
  induction t with
  | comp f g ih ih' => exact congrArgTwo Relations.comp ih ih'
  | tensor o f g ih ih' => cases o <;> exact congrArgTwo Relations.sumMap ih ih'
  | id A => rfl
  | assocR o A B C => cases o <;> rfl
  | assocL o A B C => cases o <;> rfl
  | swap o A B => cases o <;> rfl
  | diag A => rfl
  | codiag A => rfl
  | fst A B => rfl
  | snd A B => rfl
  | inl A B => rfl
  | inr A B => rfl
  | rightOut o A => cases o <;> rfl
  | rightIn o A => cases o <;> rfl
  | leftOut o A => cases o <;> rfl
  | leftIn o A => cases o <;> rfl
  | mix A B => rfl
  | dist A B C => rfl
  | zero A => rfl
  | eta p => rfl
  | epsilon p => rfl

end Term

variable {P : Type u}

theorem Derives.relation {A B : NormalForm P} {f g : Term P A B} (e : Derives f g) :
    f.relation = g.relation := by
  rw [Term.relation_toFull, Term.relation_toFull]
  exact e.toFull.relation

def occurrenceMap {A B : NormalForm P} (r : Hom A B) :
    Relations.Rel A.formula.Occ B.formula.Occ :=
  Quotient.liftOn r Term.relation (fun _ _ h => h.relation)

theorem occurrence_inclusion {A B : NormalForm P} (r : Hom A B) :
    occurrenceMap r = Presentation.occurrenceMap (inclusion r) := by
  induction r using Quotient.inductionOn with | h t =>
  exact t.relation_toFull

theorem occurrence_red {A B : Formula P} (t : Presentation.Term P A B) :
    (red t).relation = Presentation.occurrenceMap
      ((Presentation.normalization P).transport (Presentation.ofTerm t)) := by
  rw [← red_sound]
  exact (red t).relation_toFull

namespace Coordinates

open Presentation.NegationNormalization

theorem red_apply {A B : Formula P} (t : Presentation.Term P A B)
    (x : (normal A).formula.Occ) (y : (normal B).formula.Occ) :
    (red t).relation x y ↔ t.relation (fromOcc A x) (fromOcc B y) := by
  rw [occurrence_red]
  exact transport_apply (Presentation.ofTerm t) x y

theorem red_coordinates {A B : Formula P} (t : Presentation.Term P A B)
    (x : A.Occ) (y : B.Occ) :
    (red t).relation (toOcc A x) (toOcc B y) ↔ t.relation x y := by
  rw [occurrence_red]
  exact transport_coordinates (Presentation.ofTerm t) x y

end Coordinates

/-- A separately stated, unproved coherence property of the reduced syntactic quotient. -/
def Faithful (P : Type u) : Prop :=
  ∀ {A B : NormalForm P} {r s : Hom A B}, occurrenceMap r = occurrenceMap s → r = s

/-- Conditional transfer only: its premise is not supplied as a mathematical axiom. -/
theorem normal_faithful_of_reduced (hC : Faithful P) {A B : NormalForm P}
    {f g : Presentation.Hom A.formula B.formula}
    (h : Presentation.occurrenceMap f = Presentation.occurrenceMap g) : f = g := by
  obtain ⟨r, hr⟩ := representation A B f
  obtain ⟨s, hs⟩ := representation A B g
  have e : occurrenceMap r = occurrenceMap s := by
    rw [occurrence_inclusion, occurrence_inclusion, hr, hs]
    exact h
  exact hr.symm.trans ((congrArg inclusion (hC e)).trans hs)

theorem global_faithful_of_reduced (hC : Faithful P) {A B : Formula P}
    {f g : Presentation.Hom A B}
    (h : Presentation.occurrenceMap f = Presentation.occurrenceMap g) : f = g := by
  have e : Presentation.occurrenceMap ((Presentation.normalization P).transport f) =
      Presentation.occurrenceMap ((Presentation.normalization P).transport g) := by
    rw [Presentation.NegationNormalization.transport_relation,
      Presentation.NegationNormalization.transport_relation, h]
  exact (Presentation.normalization P).transport_injective (normal_faithful_of_reduced hC e)

end DosenPetric.Reduced
