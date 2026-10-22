module

public import DosenPetric.PresentationOccurrenceMap
public import DosenPetric.NormalForm

@[expose] public section

set_option autoImplicit false

namespace DosenPetric

universe u

namespace Literal

variable {P : Type u}

def flip : Literal P → Literal P
  | .pos p => .neg p
  | .neg p => .pos p

def letter : Literal P → P
  | .pos p => p
  | .neg p => p

def negative : Literal P → Bool
  | .pos _ => false
  | .neg _ => true

theorem flip_flip (l : Literal P) : l.flip.flip = l := by cases l <;> rfl

theorem letter_flip (l : Literal P) : l.flip.letter = l.letter := by cases l <;> rfl

end Literal

namespace Formula

variable {P : Type u}

/-- The letter and parity of negations on the path to a tagged occurrence. -/
def signedLabel : (A : Formula P) → A.Occ → Literal P
  | .var p, _ => .pos p
  | .top, x => nomatch x
  | .bot, x => nomatch x
  | .conj A _, .inl x => A.signedLabel x
  | .conj _ B, .inr x => B.signedLabel x
  | .disj A _, .inl x => A.signedLabel x
  | .disj _ B, .inr x => B.signedLabel x
  | .neg A, x => (A.signedLabel x).flip

def polarity (A : Formula P) (x : A.Occ) : Bool := (A.signedLabel x).negative

theorem signedLabel_letter (A : Formula P) (x : A.Occ) :
    (A.signedLabel x).letter = A.label x := by
  induction A with
  | var _ => rfl
  | top => exact Empty.elim x
  | bot => exact Empty.elim x
  | conj _ _ ih ih' => cases x with | inl x => exact ih x | inr x => exact ih' x
  | disj _ _ ih ih' => cases x with | inl x => exact ih x | inr x => exact ih' x
  | neg _ ih => exact (Literal.letter_flip _).trans (ih x)

end Formula

namespace NormalForm

variable {P : Type u}

theorem signedLabel_eq_literalAt (A : NormalForm P) (x : A.formula.Occ) :
    A.formula.signedLabel x = A.literalAt x := by
  induction A with
  | lit l => cases l <;> rfl
  | top => exact Empty.elim x
  | bot => exact Empty.elim x
  | conj _ _ ih ih' => cases x with | inl x => exact ih x | inr x => exact ih' x
  | disj _ _ ih ih' => cases x with | inl x => exact ih x | inr x => exact ih' x

end NormalForm

namespace Presentation

/-- An explicitly constructed isomorphism with invertible tagged coordinates.
The signed-label assertion concerns this comparison, not arbitrary arrows. -/
structure NormalComparison {P : Type u} (A B : Formula P) where
  forward : Hom A B
  backward : Hom B A
  forward_backward : comp forward backward = id A
  backward_forward : comp backward forward = id B
  toOcc : A.Occ → B.Occ
  fromOcc : B.Occ → A.Occ
  from_to : ∀ x, fromOcc (toOcc x) = x
  to_from : ∀ y, toOcc (fromOcc y) = y
  forward_graph : occurrenceMap forward = Relations.graph toOcc
  backward_graph : occurrenceMap backward = Relations.graph fromOcc
  signed_to : ∀ x, B.signedLabel (toOcc x) = A.signedLabel x

namespace NormalComparison

variable {P : Type u}

def refl (A : Formula P) : NormalComparison A A where
  forward := id A
  backward := id A
  forward_backward := Laws.id_comp _
  backward_forward := Laws.id_comp _
  toOcc := _root_.id
  fromOcc := _root_.id
  from_to _ := rfl
  to_from _ := rfl
  forward_graph := occurrence_id A
  backward_graph := occurrence_id A
  signed_to _ := rfl

theorem inverse_comp {A B C : Formula P} {f : Hom A B} {f' : Hom B A}
    {g : Hom B C} {g' : Hom C B} (hf : comp f f' = id A) (hg : comp g g' = id B) :
    comp (comp f g) (comp g' f') = id A := by
  rw [Laws.assoc, ← Laws.assoc g, hg, Laws.id_comp, hf]

def trans {A B C : Formula P} (e : NormalComparison A B) (d : NormalComparison B C) :
    NormalComparison A C where
  forward := comp e.forward d.forward
  backward := comp d.backward e.backward
  forward_backward := inverse_comp e.forward_backward d.forward_backward
  backward_forward := inverse_comp d.backward_forward e.backward_forward
  toOcc x := d.toOcc (e.toOcc x)
  fromOcc y := e.fromOcc (d.fromOcc y)
  from_to x := by rw [d.from_to, e.from_to]
  to_from y := by rw [e.to_from, d.to_from]
  forward_graph := by rw [occurrence_comp, e.forward_graph, d.forward_graph, Relations.graph_comp]
  backward_graph := by rw [occurrence_comp, d.backward_graph, e.backward_graph, Relations.graph_comp]
  signed_to x := (d.signed_to _).trans (e.signed_to x)

def conj {A B C D : Formula P} (e : NormalComparison A C) (d : NormalComparison B D) :
    NormalComparison (.conj A B) (.conj C D) where
  forward := tensor .conj e.forward d.forward
  backward := tensor .conj e.backward d.backward
  forward_backward := by
    rw [Laws.tensor_comp, e.forward_backward, d.forward_backward, Laws.tensor_id]
  backward_forward := by
    rw [Laws.tensor_comp, e.backward_forward, d.backward_forward, Laws.tensor_id]
  toOcc := Sum.map e.toOcc d.toOcc
  fromOcc := Sum.map e.fromOcc d.fromOcc
  from_to x := by cases x with | inl x => exact congrArg Sum.inl (e.from_to x) | inr x => exact congrArg Sum.inr (d.from_to x)
  to_from y := by cases y with | inl y => exact congrArg Sum.inl (e.to_from y) | inr y => exact congrArg Sum.inr (d.to_from y)
  forward_graph := by
    rw [occurrence_tensor_conj, e.forward_graph, d.forward_graph, Occurrence.sumMap_graph]
  backward_graph := by
    rw [occurrence_tensor_conj, e.backward_graph, d.backward_graph, Occurrence.sumMap_graph]
  signed_to x := by cases x with | inl x => exact e.signed_to x | inr x => exact d.signed_to x

def disj {A B C D : Formula P} (e : NormalComparison A C) (d : NormalComparison B D) :
    NormalComparison (.disj A B) (.disj C D) where
  forward := tensor .disj e.forward d.forward
  backward := tensor .disj e.backward d.backward
  forward_backward := by
    rw [Laws.tensor_comp, e.forward_backward, d.forward_backward, Laws.tensor_id]
  backward_forward := by
    rw [Laws.tensor_comp, e.backward_forward, d.backward_forward, Laws.tensor_id]
  toOcc := Sum.map e.toOcc d.toOcc
  fromOcc := Sum.map e.fromOcc d.fromOcc
  from_to x := by cases x with | inl x => exact congrArg Sum.inl (e.from_to x) | inr x => exact congrArg Sum.inr (d.from_to x)
  to_from y := by cases y with | inl y => exact congrArg Sum.inl (e.to_from y) | inr y => exact congrArg Sum.inr (d.to_from y)
  forward_graph := by
    rw [occurrence_tensor_disj, e.forward_graph, d.forward_graph, Occurrence.sumMap_graph]
  backward_graph := by
    rw [occurrence_tensor_disj, e.backward_graph, d.backward_graph, Occurrence.sumMap_graph]
  signed_to x := by cases x with | inl x => exact e.signed_to x | inr x => exact d.signed_to x

/-- n→/n← and their inverse equations, §14.1, printed p.310. -/
def doubleNeg (A : Formula P) : NormalComparison (.neg (.neg A)) A where
  forward := dnOut A
  backward := dnIn A
  forward_backward := Laws.dnOut_in A
  backward_forward := Laws.dnOut_out A
  toOcc := _root_.id
  fromOcc := _root_.id
  from_to _ := rfl
  to_from _ := rfl
  forward_graph := rfl
  backward_graph := rfl
  signed_to x := (Literal.flip_flip (A.signedLabel x)).symm

/-- rconj→/rconj← and their inverse equations, §14.1, printed p.310. -/
def deMorganConj (A B : Formula P) : NormalComparison (.neg (.conj A B)) (.disj (.neg A) (.neg B)) where
  forward := dmConjOut A B
  backward := dmConjIn A B
  forward_backward := Laws.dmConjOut_in A B
  backward_forward := Laws.dmConjOut_out A B
  toOcc := _root_.id
  fromOcc := _root_.id
  from_to _ := rfl
  to_from _ := rfl
  forward_graph := rfl
  backward_graph := rfl
  signed_to x := by cases x <;> rfl

/-- rdisj→/rdisj← and their inverse equations, §14.1, printed p.310. -/
def deMorganDisj (A B : Formula P) : NormalComparison (.neg (.disj A B)) (.conj (.neg A) (.neg B)) where
  forward := dmDisjOut A B
  backward := dmDisjIn A B
  forward_backward := Laws.dmDisjOut_in A B
  backward_forward := Laws.dmDisjOut_out A B
  toOcc := _root_.id
  fromOcc := _root_.id
  from_to _ := rfl
  to_from _ := rfl
  forward_graph := rfl
  backward_graph := rfl
  signed_to x := by cases x <;> rfl

/-- The constant comparison ρ and its two inverse equations, printed p.312. -/
def negTop : NormalComparison (.neg (.top : Formula P)) .bot where
  forward := negTopOut
  backward := negTopIn
  forward_backward := Laws.negTopOut_in
  backward_forward := Laws.negTopOut_out
  toOcc := _root_.id
  fromOcc := _root_.id
  from_to x := Empty.elim x
  to_from y := Empty.elim y
  forward_graph := rfl
  backward_graph := rfl
  signed_to x := Empty.elim x

/-- The constant comparison ρ and its two inverse equations, printed p.312. -/
def negBot : NormalComparison (.neg (.bot : Formula P)) .top where
  forward := negBotOut
  backward := negBotIn
  forward_backward := Laws.negBotOut_in
  backward_forward := Laws.negBotOut_out
  toOcc := _root_.id
  fromOcc := _root_.id
  from_to x := Empty.elim x
  to_from y := Empty.elim y
  forward_graph := rfl
  backward_graph := rfl
  signed_to x := Empty.elim x

theorem signed_from {A B : Formula P} (e : NormalComparison A B) (y : B.Occ) :
    A.signedLabel (e.fromOcc y) = B.signedLabel y := by
  have h := e.signed_to (e.fromOcc y)
  rw [e.to_from] at h
  exact h.symm

theorem toOcc_injective {A B : Formula P} (e : NormalComparison A B) {x y : A.Occ}
    (h : e.toOcc x = e.toOcc y) : x = y := by
  have h' := congrArg e.fromOcc h
  rw [e.from_to, e.from_to] at h'
  exact h'

end NormalComparison

end Presentation
end DosenPetric
