module

public import DosenPetric.Category

@[expose] public section
set_option autoImplicit false
namespace DosenPetric
universe u v w x y z

structure Functor {O : Type u} {Q : Type v} (C : Category.{u,w} O) (D : Category.{v,x} Q) where
  obj : O → Q
  map : {A B : O} → C.Hom A B → D.Hom (obj A) (obj B)
  map_id : ∀ A, map (C.id A) = D.id (obj A)
  map_comp : ∀ {A B E} (f : C.Hom A B) (g : C.Hom B E), map (C.comp f g) = D.comp (map f) (map g)

namespace Functor
variable {O : Type u} {Q : Type v} {R : Type y}
  {C : Category.{u,w} O} {D : Category.{v,x} Q} {E : Category.{y,z} R}

def identity (C : Category.{u,w} O) : Functor C C where
  obj A := A
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

def comp (F : Functor C D) (G : Functor D E) : Functor C E where
  obj A := G.obj (F.obj A)
  map f := G.map (F.map f)
  map_id A := by rw [F.map_id,G.map_id]
  map_comp f g := by rw [F.map_comp,G.map_comp]

end Functor

structure NaturalTransformation {O : Type u} {Q : Type v}
    {C : Category.{u,w} O} {D : Category.{v,x} Q} (F G : Functor C D) where
  app : (A : O) → D.Hom (F.obj A) (G.obj A)
  natural : ∀ {A B} (f : C.Hom A B), D.comp (F.map f) (app B) = D.comp (app A) (G.map f)

structure NaturalIsomorphism {O : Type u} {Q : Type v}
    {C : Category.{u,w} O} {D : Category.{v,x} Q} (F G : Functor C D) where
  hom : NaturalTransformation F G
  inv : NaturalTransformation G F
  hom_inv : ∀ A, D.comp (hom.app A) (inv.app A) = D.id (F.obj A)
  inv_hom : ∀ A, D.comp (inv.app A) (hom.app A) = D.id (G.obj A)

end DosenPetric
