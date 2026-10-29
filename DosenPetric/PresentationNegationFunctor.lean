module

public import DosenPetric.ReducedDualFunctor
public import DosenPetric.ReducedRecovery

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}
open Presentation.NegationNormalization (normal form_true)

/-- Reflect the normalized source arrow at the normal forms of its negated endpoints. -/
def negReduceHom {A B : Formula P} (f : Presentation.Hom A B) : Hom (normal (.neg B)) (normal (.neg A)) :=
  castHom (form_true B).symm (form_true A).symm (dualHom (reduceHom f))

theorem negReduceHom_id (A : Formula P) : negReduceHom (Presentation.id A) = id (normal (.neg A)) := by
  erw [negReduceHom,reduceHom_id,dualHom_id,castHom_id]

theorem negReduceHom_comp {A B C : Formula P} (f : Presentation.Hom A B) (g : Presentation.Hom B C) :
    negReduceHom (Presentation.comp f g) = comp (negReduceHom g) (negReduceHom f) := by
  rw [negReduceHom,reduceHom_comp,dualHom_comp,
    castHom_comp (form_true C).symm (form_true B).symm (form_true A).symm]
  rfl

end DosenPetric.Reduced
namespace DosenPetric.Presentation
universe u
variable {P : Type u}

/-- Derived arrow negation in the actual source quotient. -/
def negate {A B : Formula P} (f : Hom A B) : Hom (.neg B) (.neg A) :=
  Reduced.recoverHom (Reduced.negReduceHom f)

theorem negate_id (A : Formula P) : negate (id A) = id (.neg A) := by
  rw [negate,Reduced.negReduceHom_id,Reduced.recoverHom_id]

theorem negate_comp {A B C : Formula P} (f : Hom A B) (g : Hom B C) :
    negate (comp f g) = comp (negate g) (negate f) := by
  rw [negate,Reduced.negReduceHom_comp,Reduced.recoverHom_comp]
  rfl

def negationFunctor (P : Type u) : Functor (opposite (category P)) (category P) where
  obj := Formula.neg
  map := negate
  map_id := negate_id
  map_comp f g := negate_comp g f

end DosenPetric.Presentation
