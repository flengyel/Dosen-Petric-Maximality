module

public import DosenPetric.PresentationConsequences

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.PresentationSemantics
universe u v

/-- Object operations of the complete source signature in a target category. -/
structure Objects (X : Type u) where
  conj : X → X → X
  disj : X → X → X
  top : X
  bot : X
  neg : X → X

namespace Objects
variable {X : Type u} (O : Objects X)
abbrev bin : Presentation.Op → X → X → X
  | .conj => O.conj
  | .disj => O.disj
abbrev unit : Presentation.Op → X
  | .conj => O.top
  | .disj => O.bot
end Objects

/-- Every primitive arrow family of C(B), with its target object types.
Identities and composition belong to C. Arrow negation remains the explicit
source-derived operation, not an additional primitive constructor. -/
structure Primitives {X : Type u} (C : Category.{u,v} X) (O : Objects X) where
  tensor : ∀ o {A B D E : X}, C.Hom A D → C.Hom B E → C.Hom (O.bin o A B) (O.bin o D E)
  assocR : ∀ o A B D, C.Hom (O.bin o A (O.bin o B D)) (O.bin o (O.bin o A B) D)
  assocL : ∀ o A B D, C.Hom (O.bin o (O.bin o A B) D) (O.bin o A (O.bin o B D))
  swap : ∀ o A B, C.Hom (O.bin o A B) (O.bin o B A)
  diag : ∀ A, C.Hom A (O.conj A A)
  codiag : ∀ A, C.Hom (O.disj A A) A
  fst : ∀ A B, C.Hom (O.conj A B) A
  snd : ∀ A B, C.Hom (O.conj A B) B
  inl : ∀ A B, C.Hom A (O.disj A B)
  inr : ∀ A B, C.Hom B (O.disj A B)
  rightOut : ∀ o A, C.Hom (O.bin o A (O.unit o)) A
  rightIn : ∀ o A, C.Hom A (O.bin o A (O.unit o))
  leftOut : ∀ o A, C.Hom (O.bin o (O.unit o) A) A
  leftIn : ∀ o A, C.Hom A (O.bin o (O.unit o) A)
  mix : ∀ A B, C.Hom (O.conj A B) (O.disj A B)
  dist : ∀ A B D, C.Hom (O.conj A (O.disj B D)) (O.disj (O.conj A B) D)
  zero : ∀ A, C.Hom A A
  dnOut : ∀ A, C.Hom (O.neg (O.neg A)) A
  dnIn : ∀ A, C.Hom A (O.neg (O.neg A))
  dmConjOut : ∀ A B, C.Hom (O.neg (O.conj A B)) (O.disj (O.neg A) (O.neg B))
  dmConjIn : ∀ A B, C.Hom (O.disj (O.neg A) (O.neg B)) (O.neg (O.conj A B))
  dmDisjOut : ∀ A B, C.Hom (O.neg (O.disj A B)) (O.conj (O.neg A) (O.neg B))
  dmDisjIn : ∀ A B, C.Hom (O.conj (O.neg A) (O.neg B)) (O.neg (O.disj A B))
  negTopOut : C.Hom (O.neg O.top) O.bot
  negTopIn : C.Hom O.bot (O.neg O.top)
  negBotOut : C.Hom (O.neg O.bot) O.top
  negBotIn : C.Hom O.top (O.neg O.bot)
  excludedMiddle : ∀ A, C.Hom O.top (O.disj (O.neg A) A)
  contradiction : ∀ A, C.Hom (O.conj A (O.neg A)) O.bot

end DosenPetric.PresentationSemantics
