module

public import DosenPetric.ReducedQuotientReduction
public import DosenPetric.CategoryFunctor

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}
open Presentation.NegationNormalization (normal)

def reductionFunctor (P : Type u) : Functor (Presentation.category P) (category P) where
  obj := normal
  map := reduceHom
  map_id := reduceHom_id
  map_comp := reduceHom_comp

def inclusionFunctor (P : Type u) : Functor (category P) (Presentation.category P) where
  obj := NormalForm.formula
  map := inclusion
  map_id := inclusion_id
  map_comp := inclusion_comp

theorem normalization_forward_natural {A B : Formula P} (f : Presentation.Hom A B) :
    Presentation.comp f (Presentation.NegationNormalization.forward B) =
      Presentation.comp (Presentation.NegationNormalization.forward A) (inclusion (reduceHom f)) := by
  rw [inclusion_reduceHom]
  change Presentation.comp f (Presentation.NegationNormalization.forward B) =
    Presentation.comp (Presentation.NegationNormalization.forward A)
      (Presentation.comp (Presentation.comp (Presentation.NegationNormalization.backward A) f)
        (Presentation.NegationNormalization.forward B))
  rw [← Presentation.Laws.assoc,← Presentation.Laws.assoc,
    Presentation.NegationNormalization.forward_backward,Presentation.Laws.id_comp]

theorem normalization_backward_natural {A B : Formula P} (f : Presentation.Hom A B) :
    Presentation.comp (inclusion (reduceHom f)) (Presentation.NegationNormalization.backward B) =
      Presentation.comp (Presentation.NegationNormalization.backward A) f := by
  rw [inclusion_reduceHom]
  change Presentation.comp
    (Presentation.comp (Presentation.comp (Presentation.NegationNormalization.backward A) f)
      (Presentation.NegationNormalization.forward B)) (Presentation.NegationNormalization.backward B) = _
  rw [Presentation.Laws.assoc,Presentation.NegationNormalization.forward_backward,Presentation.Laws.comp_id]

def normalizationNaturalIso (P : Type u) :
    NaturalIsomorphism (Functor.identity (Presentation.category P))
      ((reductionFunctor P).comp (inclusionFunctor P)) where
  hom := ⟨Presentation.NegationNormalization.forward,normalization_forward_natural⟩
  inv := ⟨Presentation.NegationNormalization.backward,normalization_backward_natural⟩
  hom_inv := Presentation.NegationNormalization.forward_backward
  inv_hom := Presentation.NegationNormalization.backward_forward

def castHom {A B A' B' : NormalForm P} (hA : A = A') (hB : B = B') (f : Hom A B) : Hom A' B' :=
  hA ▸ hB ▸ f

theorem inclusion_castHom {A B A' B' : NormalForm P} (hA : A = A') (hB : B = B') (f : Hom A B) :
    inclusion (castHom hA hB f) =
      Presentation.castHom (congrArg NormalForm.formula hA) (congrArg NormalForm.formula hB) (inclusion f) := by
  cases hA
  cases hB
  rfl

theorem reduction_inclusion {A B : NormalForm P} (f : Hom A B) :
    castHom (Presentation.NegationNormalization.normal_formula A)
      (Presentation.NegationNormalization.normal_formula B) (reduceHom (inclusion f)) = f := by
  apply inclusion_injective
  rw [inclusion_castHom,inclusion_reduceHom]
  exact Presentation.NegationNormalization.transport_formula A B (inclusion f)

end DosenPetric.Reduced
