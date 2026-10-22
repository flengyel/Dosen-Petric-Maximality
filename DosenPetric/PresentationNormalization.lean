module

public import DosenPetric.NormalizationComparison

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.Presentation

universe u

namespace NegationNormalization

variable {P : Type u}

/-- False normalizes A; true normalizes neg A. Recursion is on A alone. -/
def form : Formula P → Bool → NormalForm P
  | .var p, false => .lit (.pos p)
  | .var p, true => .lit (.neg p)
  | .top, false => .top
  | .top, true => .bot
  | .bot, false => .bot
  | .bot, true => .top
  | .conj A B, false => .conj (form A false) (form B false)
  | .conj A B, true => .disj (form A true) (form B true)
  | .disj A B, false => .disj (form A false) (form B false)
  | .disj A B, true => .conj (form A true) (form B true)
  | .neg A, false => form A true
  | .neg A, true => form A false

abbrev source (A : Formula P) : Bool → Formula P
  | false => A
  | true => .neg A

/-- The comparisons i_A and i_A^{-1}, §14.1, printed pp.313–314.
Only n-r/rho inverses, composition, and the two covariant tensors are used. -/
def comparison : (A : Formula P) → (s : Bool) →
    NormalComparison (source A s) (form A s).formula
  | .var p, false => .refl (.var p)
  | .var p, true => .refl (.neg (.var p))
  | .top, false => .refl .top
  | .top, true => .negTop
  | .bot, false => .refl .bot
  | .bot, true => .negBot
  | .conj A B, false => .conj (comparison A false) (comparison B false)
  | .conj A B, true =>
    .trans (.deMorganConj A B) (.disj (comparison A true) (comparison B true))
  | .disj A B, false => .disj (comparison A false) (comparison B false)
  | .disj A B, true =>
    .trans (.deMorganDisj A B) (.conj (comparison A true) (comparison B true))
  | .neg A, false => comparison A true
  | .neg A, true => .trans (.doubleNeg A) (comparison A false)

def normal (A : Formula P) : NormalForm P := form A false

def forward (A : Formula P) : Hom A (normal A).formula := (comparison A false).forward

def backward (A : Formula P) : Hom (normal A).formula A := (comparison A false).backward

theorem forward_backward (A : Formula P) : comp (forward A) (backward A) = id A :=
  (comparison A false).forward_backward

theorem backward_forward (A : Formula P) :
    comp (backward A) (forward A) = id (normal A).formula :=
  (comparison A false).backward_forward

/-- Coordinates preserve branch tags; negative recursion changes only the literal sign. -/
def toOcc (A : Formula P) : A.Occ → (normal A).formula.Occ := (comparison A false).toOcc

def fromOcc (A : Formula P) : (normal A).formula.Occ → A.Occ := (comparison A false).fromOcc

theorem from_to (A : Formula P) (x : A.Occ) : fromOcc A (toOcc A x) = x :=
  (comparison A false).from_to x

theorem to_from (A : Formula P) (y : (normal A).formula.Occ) : toOcc A (fromOcc A y) = y :=
  (comparison A false).to_from y

theorem forward_graph (A : Formula P) : occurrenceMap (forward A) = Relations.graph (toOcc A) :=
  (comparison A false).forward_graph

theorem backward_graph (A : Formula P) : occurrenceMap (backward A) = Relations.graph (fromOcc A) :=
  (comparison A false).backward_graph

/-- The full signed literal, including the letter, is preserved by this normalizer. -/
theorem literal_toOcc (A : Formula P) (x : A.Occ) :
    (normal A).literalAt (toOcc A x) = A.signedLabel x := by
  rw [← NormalForm.signedLabel_eq_literalAt]
  exact (comparison A false).signed_to x

theorem literal_fromOcc (A : Formula P) (y : (normal A).formula.Occ) :
    A.signedLabel (fromOcc A y) = (normal A).literalAt y := by
  rw [← NormalForm.signedLabel_eq_literalAt]
  exact (comparison A false).signed_from y

theorem label_toOcc (A : Formula P) (x : A.Occ) :
    (normal A).formula.label (toOcc A x) = A.label x := by
  exact (Formula.signedLabel_letter _ _).symm.trans
    ((congrArg Literal.letter ((comparison A false).signed_to x)).trans
      (Formula.signedLabel_letter A x))

theorem label_fromOcc (A : Formula P) (y : (normal A).formula.Occ) :
    A.label (fromOcc A y) = (normal A).formula.label y := by
  exact (Formula.signedLabel_letter _ _).symm.trans
    ((congrArg Literal.letter ((comparison A false).signed_from y)).trans
      (Formula.signedLabel_letter _ y))

theorem polarity_toOcc (A : Formula P) (x : A.Occ) :
    ((normal A).literalAt (toOcc A x)).negative = A.polarity x :=
  congrArg Literal.negative (literal_toOcc A x)

theorem polarity_fromOcc (A : Formula P) (y : (normal A).formula.Occ) :
    A.polarity (fromOcc A y) = ((normal A).literalAt y).negative :=
  congrArg Literal.negative (literal_fromOcc A y)

theorem toOcc_injective (A : Formula P) {x y : A.Occ} (h : toOcc A x = toOcc A y) : x = y :=
  (comparison A false).toOcc_injective h

/-- Empty occurrence sets stay empty, including formulas built only from constants. -/
theorem no_occ {A : Formula P} (h : A.Occ → False) (y : (normal A).formula.Occ) : False :=
  h (fromOcc A y)

theorem top_no_occ (y : (normal (.top : Formula P)).formula.Occ) : False := Empty.elim y

theorem bot_no_occ (y : (normal (.bot : Formula P)).formula.Occ) : False := Empty.elim y

theorem negTop_no_occ (y : (normal (.neg (.top : Formula P))).formula.Occ) : False := Empty.elim y

theorem negBot_no_occ (y : (normal (.neg (.bot : Formula P))).formula.Occ) : False := Empty.elim y

/-- Even below a negation, repeated letters have distinct normal-form positions. -/
theorem repeated_negative_tags (p : P) :
    toOcc (.neg (.conj (.var p) (.var p))) (.inl ()) ≠
      toOcc (.neg (.conj (.var p) (.var p))) (.inr ()) := by
  intro h
  have h' := toOcc_injective _ h
  cases h'

end NegationNormalization

/-- The existing Normalization interface, instantiated in the published equation quotient. -/
def normalization (P : Type u) : Normalization (category P) where
  normal := NegationNormalization.normal
  forward := NegationNormalization.forward
  backward := NegationNormalization.backward
  forward_backward := NegationNormalization.forward_backward
  backward_forward := NegationNormalization.backward_forward

namespace NegationNormalization

variable {P : Type u}

theorem transport_relation {A B : Formula P} (f : Hom A B) :
    occurrenceMap ((normalization P).transport f) =
      Relations.comp (Relations.comp (Relations.graph (fromOcc A)) (occurrenceMap f))
        (Relations.graph (toOcc B)) := by
  change occurrenceMap (comp (comp (backward A) f) (forward B)) = _
  rw [occurrence_comp, occurrence_comp, backward_graph, forward_graph]

/-- The transported relation is the original relation in the inverse coordinates. -/
theorem transport_apply {A B : Formula P} (f : Hom A B)
    (x : (normal A).formula.Occ) (y : (normal B).formula.Occ) :
    occurrenceMap ((normalization P).transport f) x y ↔
      occurrenceMap f (fromOcc A x) (fromOcc B y) := by
  rw [transport_relation]
  change (∃ z, (∃ a, fromOcc A x = a ∧ occurrenceMap f a z) ∧ toOcc B z = y) ↔ _
  constructor
  · rintro ⟨z, ⟨a, ha, h⟩, hz⟩
    cases ha
    have he : z = fromOcc B y := by
      calc
        z = fromOcc B (toOcc B z) := (from_to B z).symm
        _ = fromOcc B y := congrArg (fromOcc B) hz
    rw [← he]
    exact h
  · intro h
    exact ⟨fromOcc B y, ⟨fromOcc A x, rfl, h⟩, to_from B y⟩

theorem transport_coordinates {A B : Formula P} (f : Hom A B) (x : A.Occ) (y : B.Occ) :
    occurrenceMap ((normalization P).transport f) (toOcc A x) (toOcc B y) ↔
      occurrenceMap f x y := by
  rw [transport_apply, from_to, from_to]

/-- Recovery is the existing structural theorem, using the constructed inverse arrows. -/
theorem transport_recover {A B : Formula P} (f : Hom A B) :
    comp (comp (forward A) ((normalization P).transport f)) (backward B) = f :=
  (normalization P).recover f

theorem transport_injective {A B : Formula P} {f g : Hom A B}
    (h : (normalization P).transport f = (normalization P).transport g) : f = g :=
  (normalization P).transport_injective h

end NegationNormalization
end DosenPetric.Presentation
