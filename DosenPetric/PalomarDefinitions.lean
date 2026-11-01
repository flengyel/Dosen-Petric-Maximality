module

public import DosenPetric.PresentationSubstitution

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Palomar
universe u
open Presentation

/-- An equivalence relation on parallel arrow terms that contains every
defining equation and is preserved by composition, conjunction and
disjunction. -/
structure PrimitiveCongruence (P : Type u) where
  Rel : {A B : Formula P} → Term P A B → Term P A B → Prop
  refl : ∀ {A B} (f : Term P A B), Rel f f
  symm : ∀ {A B} {f g : Term P A B}, Rel f g → Rel g f
  trans : ∀ {A B} {f g h : Term P A B}, Rel f g → Rel g h → Rel f h
  equation : ∀ {A B} {f g : Term P A B}, Equation f g → Rel f g
  comp : ∀ {A B C} {f f' : Term P A B} {g g' : Term P B C},
    Rel f f' → Rel g g' → Rel (Term.comp f g) (Term.comp f' g')
  tensor : ∀ o {A B C D} {f f' : Term P A C} {g g' : Term P B D},
    Rel f f' → Rel g g' → Rel (Term.tensor o f g) (Term.tensor o f' g')

namespace PrimitiveCongruence
variable {P : Type u} (R : PrimitiveCongruence P)

/-- A congruence is closed under uniform substitution if it relates the
substituted terms whenever it relates the original terms. Substitution acts
on both endpoint formulas as well. -/
def Closed : Prop := ∀ (σ : P → Formula P) {A B} {f g : Term P A B},
  R.Rel f g → R.Rel (f.subst σ) (g.subst σ)

/-- A congruence is total if it relates every pair of parallel arrow terms. -/
def Total : Prop := ∀ {A B} (f g : Term P A B), R.Rel f g

end PrimitiveCongruence
end DosenPetric.Palomar
