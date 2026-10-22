module

public import Init

@[expose] public section

set_option autoImplicit false

namespace DosenPetric

universe u v

/-- Composition `comp f g` applies `f` first, then `g`. -/
structure Category (Obj : Type u) where
  Hom : Obj → Obj → Type v
  id : (A : Obj) → Hom A A
  comp : {A B C : Obj} → Hom A B → Hom B C → Hom A C
  id_comp : ∀ {A B} (f : Hom A B), comp (id A) f = f
  comp_id : ∀ {A B} (f : Hom A B), comp f (id B) = f
  assoc : ∀ {A B C D} (f : Hom A B) (g : Hom B C) (h : Hom C D),
    comp (comp f g) h = comp f (comp g h)

/-- The zero-identity law does not require any previously empty hom-set to be inhabited. -/
structure ZeroIdentity {Obj : Type u} (C : Category.{u,v} Obj) where
  zero : (A : Obj) → C.Hom A A
  law : ∀ {A B} (f g : C.Hom A B), C.comp (zero A) f = C.comp g (zero B)

namespace ZeroIdentity

variable {Obj : Type u} {C : Category.{u,v} Obj} (Z : ZeroIdentity C)

/-- A zero arrow is defined using an existing arrow with the required endpoints. -/
def zeroOf {A B : Obj} (f : C.Hom A B) : C.Hom A B := C.comp (Z.zero A) f

theorem zeroOf_independent {A B : Obj} (f g : C.Hom A B) :
    Z.zeroOf f = Z.zeroOf g :=
  (Z.law f g).trans (Z.law g g).symm

theorem commute {A B : Obj} (f : C.Hom A B) :
    C.comp (Z.zero A) f = C.comp f (Z.zero B) := Z.law f f

theorem postcompose {A B D : Obj} (f : C.Hom A B) (h : C.Hom B D) :
    C.comp (Z.zeroOf f) h = Z.zeroOf (C.comp f h) :=
  C.assoc (Z.zero A) f h

theorem precompose {X A B : Obj} (k : C.Hom X A) (f : C.Hom A B) :
    C.comp k (Z.zeroOf f) = Z.zeroOf (C.comp k f) := by
  unfold zeroOf
  rw [← C.assoc, ← Z.commute k, C.assoc]

theorem zero_idempotent (A : Obj) : C.comp (Z.zero A) (Z.zero A) = Z.zero A := by
  have h := Z.law (Z.zero A) (C.id A)
  exact h.trans (C.id_comp (Z.zero A))

end ZeroIdentity

end DosenPetric
