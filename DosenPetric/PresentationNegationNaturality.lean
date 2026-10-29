module

public import DosenPetric.ReducedNegationLaws

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation
universe u
variable {P : Type u}

theorem dnOut_natural {A B : Formula P} (f : Hom A B) :
    comp (negate (negate f)) (dnOut B) = comp (dnOut A) f := by
  apply Reduced.reduceHom_injective
  rw [Reduced.reduceHom_comp,Reduced.reduceHom_comp,Reduced.reduce_negate,
    Reduced.negReduceHom_twice]
  change Reduced.comp (Reduced.reduceHom f) (Reduced.id _) =
    Reduced.comp (Reduced.id _) (Reduced.reduceHom f)
  rw [Reduced.Laws.comp_id,Reduced.Laws.id_comp]

theorem dnIn_natural {A B : Formula P} (f : Hom A B) :
    comp f (dnIn B) = comp (dnIn A) (negate (negate f)) := by
  apply Reduced.reduceHom_injective
  rw [Reduced.reduceHom_comp,Reduced.reduceHom_comp,Reduced.reduce_negate,
    Reduced.negReduceHom_twice]
  change Reduced.comp (Reduced.reduceHom f) (Reduced.id _) =
    Reduced.comp (Reduced.id _) (Reduced.reduceHom f)
  rw [Reduced.Laws.comp_id,Reduced.Laws.id_comp]

theorem dmConjOut_natural {A B C D : Formula P} (f : Hom A C) (g : Hom B D) :
    comp (negate (tensor .conj f g)) (dmConjOut A B) =
      comp (dmConjOut C D) (tensor .disj (negate f) (negate g)) := by
  apply Reduced.reduceHom_injective
  rw [Reduced.reduceHom_comp,Reduced.reduceHom_comp,Reduced.reduce_negate,
    Reduced.negReduceHom_tensor_conj,Reduced.reduceHom_tensor_disj,
    Reduced.reduce_negate,Reduced.reduce_negate]
  change Reduced.comp _ (Reduced.id _) = Reduced.comp (Reduced.id _) _
  rw [Reduced.Laws.comp_id,Reduced.Laws.id_comp]

theorem dmConjIn_natural {A B C D : Formula P} (f : Hom A C) (g : Hom B D) :
    comp (tensor .disj (negate f) (negate g)) (dmConjIn A B) =
      comp (dmConjIn C D) (negate (tensor .conj f g)) := by
  apply Reduced.reduceHom_injective
  rw [Reduced.reduceHom_comp,Reduced.reduceHom_comp,Reduced.reduce_negate,
    Reduced.negReduceHom_tensor_conj,Reduced.reduceHom_tensor_disj,
    Reduced.reduce_negate,Reduced.reduce_negate]
  change Reduced.comp _ (Reduced.id _) = Reduced.comp (Reduced.id _) _
  rw [Reduced.Laws.comp_id,Reduced.Laws.id_comp]

theorem dmDisjOut_natural {A B C D : Formula P} (f : Hom A C) (g : Hom B D) :
    comp (negate (tensor .disj f g)) (dmDisjOut A B) =
      comp (dmDisjOut C D) (tensor .conj (negate f) (negate g)) := by
  apply Reduced.reduceHom_injective
  rw [Reduced.reduceHom_comp,Reduced.reduceHom_comp,Reduced.reduce_negate,
    Reduced.negReduceHom_tensor_disj,Reduced.reduceHom_tensor_conj,
    Reduced.reduce_negate,Reduced.reduce_negate]
  change Reduced.comp _ (Reduced.id _) = Reduced.comp (Reduced.id _) _
  rw [Reduced.Laws.comp_id,Reduced.Laws.id_comp]

theorem dmDisjIn_natural {A B C D : Formula P} (f : Hom A C) (g : Hom B D) :
    comp (tensor .conj (negate f) (negate g)) (dmDisjIn A B) =
      comp (dmDisjIn C D) (negate (tensor .disj f g)) := by
  apply Reduced.reduceHom_injective
  rw [Reduced.reduceHom_comp,Reduced.reduceHom_comp,Reduced.reduce_negate,
    Reduced.negReduceHom_tensor_disj,Reduced.reduceHom_tensor_conj,
    Reduced.reduce_negate,Reduced.reduce_negate]
  change Reduced.comp _ (Reduced.id _) = Reduced.comp (Reduced.id _) _
  rw [Reduced.Laws.comp_id,Reduced.Laws.id_comp]

/-- Double negation is naturally isomorphic to the identity in the actual quotient. -/
def doubleNegationFunctor (P : Type u) : Functor (category P) (category P) where
  obj A := .neg (.neg A)
  map f := negate (negate f)
  map_id A := by
    change negate (negate (id A)) = id _
    rw [negate_id,negate_id]
  map_comp f g := by
    change negate (negate (comp f g)) = comp (negate (negate f)) (negate (negate g))
    rw [negate_comp,negate_comp]

def doubleNegationNaturalIso (P : Type u) :
    NaturalIsomorphism (doubleNegationFunctor P) (Functor.identity (category P)) where
  hom := ⟨dnOut,dnOut_natural⟩
  inv := ⟨dnIn,dnIn_natural⟩
  hom_inv := Laws.dnOut_in
  inv_hom := Laws.dnOut_out

end DosenPetric.Presentation
