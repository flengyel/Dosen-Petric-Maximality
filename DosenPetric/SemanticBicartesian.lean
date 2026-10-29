module

public import DosenPetric.SemanticInterpretationEvaluation

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.PresentationSemantics
universe u v w
variable {X : Type u} {C : Category.{u,v} X} {O : Objects X}

namespace Primitives
variable (S : Primitives C O)

def pair {Y A B : X} (f : C.Hom Y A) (g : C.Hom Y B) : C.Hom Y (O.conj A B) :=
  C.comp (S.diag Y) (S.tensor .conj f g)

def copair {A B Y : X} (f : C.Hom A Y) (g : C.Hom B Y) : C.Hom (O.disj A B) Y :=
  C.comp (S.tensor .disj f g) (S.codiag Y)

def toTop (A : X) : C.Hom A O.top := C.comp (S.rightIn .conj A) (S.snd A O.top)
def fromBot (A : X) : C.Hom O.bot A := C.comp (S.inr A O.bot) (S.rightOut .disj A)

end Primitives

/-- The target products, coproducts and units have their genuine universal
properties on all target arrows, including arrows outside any interpretation's image. -/
structure BicartesianLaws (S : Primitives C O) : Prop where
  pair_fst : ∀ {Y A B} (f : C.Hom Y A) (g : C.Hom Y B), C.comp (S.pair f g) (S.fst A B) = f
  pair_snd : ∀ {Y A B} (f : C.Hom Y A) (g : C.Hom Y B), C.comp (S.pair f g) (S.snd A B) = g
  pair_eta : ∀ {Y A B} (f : C.Hom Y (O.conj A B)), S.pair (C.comp f (S.fst A B)) (C.comp f (S.snd A B)) = f
  inl_copair : ∀ {A B Y} (f : C.Hom A Y) (g : C.Hom B Y), C.comp (S.inl A B) (S.copair f g) = f
  inr_copair : ∀ {A B Y} (f : C.Hom A Y) (g : C.Hom B Y), C.comp (S.inr A B) (S.copair f g) = g
  copair_eta : ∀ {A B Y} (f : C.Hom (O.disj A B) Y), S.copair (C.comp (S.inl A B) f) (C.comp (S.inr A B) f) = f
  toTop_unique : ∀ {A} (f : C.Hom A O.top), f = S.toTop A
  fromBot_unique : ∀ {A} (f : C.Hom O.bot A), f = S.fromBot A

/-- A target model satisfies the complete source presentation, its native
bicartesian universal properties and the zero-identity law on existing arrows. -/
structure Model (P : Type w) (S : Primitives C O) : Prop where
  equations : S.SatisfiesTheory P
  bicartesian : BicartesianLaws S
  zero_identity : ∀ {A B : X} (f g : C.Hom A B), C.comp (S.zero A) f = C.comp g (S.zero B)

namespace Model
variable {P : Type w} {S : Primitives C O}

def zeroIdentity (M : Model P S) : ZeroIdentity C where
  zero := S.zero
  law := M.zero_identity

end Model
end DosenPetric.PresentationSemantics
