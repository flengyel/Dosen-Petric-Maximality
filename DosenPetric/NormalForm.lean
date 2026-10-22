module

public import DosenPetric.Collapse

@[expose] public section

set_option autoImplicit false

namespace DosenPetric

universe u v

inductive Literal (P : Type u) where
  | pos : P → Literal P
  | neg : P → Literal P

namespace Literal

abbrev formula {P : Type u} : Literal P → Formula P
  | .pos p => .var p
  | .neg p => .neg (.var p)

def point {P : Type u} (l : Literal P) : l.formula.Occ := by
  cases l <;> exact ()

theorem occ_unique {P : Type u} (l : Literal P) (x : l.formula.Occ) : x = l.point := by
  cases l <;> cases x <;> rfl

end Literal

/-- A normal form has negation only at variable leaves. -/
inductive NormalForm (P : Type u) where
  | lit : Literal P → NormalForm P
  | top : NormalForm P
  | bot : NormalForm P
  | conj : NormalForm P → NormalForm P → NormalForm P
  | disj : NormalForm P → NormalForm P → NormalForm P

namespace NormalForm

variable {P : Type u}

abbrev formula : NormalForm P → Formula P
  | .lit l => l.formula
  | .top => .top
  | .bot => .bot
  | .conj A B => .conj A.formula B.formula
  | .disj A B => .disj A.formula B.formula

abbrev literalAt : (A : NormalForm P) → A.formula.Occ → Literal P
  | .lit l, _ => l
  | .top, x => nomatch x
  | .bot, x => nomatch x
  | .conj A _, .inl x => A.literalAt x
  | .conj _ B, .inr x => B.literalAt x
  | .disj A _, .inl x => A.literalAt x
  | .disj _ B, .inr x => B.literalAt x

end NormalForm

/-- Normalization is specified by actual inverse arrows of the original category. -/
structure Normalization {P : Type u} (C : Category.{u,v} (Formula P)) where
  normal : Formula P → NormalForm P
  forward : (A : Formula P) → C.Hom A (normal A).formula
  backward : (A : Formula P) → C.Hom (normal A).formula A
  forward_backward : ∀ A, C.comp (forward A) (backward A) = C.id A
  backward_forward : ∀ A, C.comp (backward A) (forward A) = C.id (normal A).formula

namespace Normalization

variable {P : Type u} {C : Category.{u,v} (Formula P)} (N : Normalization C)

def transport {A B : Formula P} (f : C.Hom A B) : C.Hom (N.normal A).formula (N.normal B).formula :=
  C.comp (C.comp (N.backward A) f) (N.forward B)

theorem recover {A B : Formula P} (f : C.Hom A B) :
    C.comp (C.comp (N.forward A) (N.transport f)) (N.backward B) = f := by
  unfold transport
  rw [← C.assoc (N.forward A) _ (N.forward B),
    ← C.assoc (N.forward A) (N.backward A) f, N.forward_backward, C.id_comp,
    C.assoc, N.forward_backward, C.comp_id]

theorem transport_injective {A B : Formula P} {f g : C.Hom A B}
    (h : N.transport f = N.transport g) : f = g := by
  have hh := congrArg (fun t => C.comp (C.comp (N.forward A) t) (N.backward B)) h
  rw [N.recover, N.recover] at hh
  exact hh

end Normalization

/-- Edges between normal forms preserve the entire signed literal. -/
def SignedLabelPreservation {P : Type u} {C : Category.{u,v} (Formula P)}
    {S : Structure C} {Z : ZeroIdentity C} (I : OccurrenceInterpretation S Z) : Prop :=
  ∀ (A B : NormalForm P) (f : C.Hom A.formula B.formula)
    (x : A.formula.Occ) (y : B.formula.Occ),
    I.map f x y → A.literalAt x = B.literalAt y

end DosenPetric
