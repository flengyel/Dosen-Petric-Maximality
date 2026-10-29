module

public import DosenPetric.ReducedReductionFunctor

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}
open Presentation.NegationNormalization (normal)

theorem castHom_id {A B : NormalForm P} (h : A = B) : castHom h h (id A) = id B := by
  cases h
  rfl

theorem castHom_comp {A B C A' B' C' : NormalForm P} (hA : A = A') (hB : B = B') (hC : C = C')
    (f : Hom A B) (g : Hom B C) :
    castHom hA hC (comp f g) = comp (castHom hA hB f) (castHom hB hC g) := by
  cases hA
  cases hB
  cases hC
  rfl

/-- Recover a source arrow from its exact normalized quotient endpoints. -/
def recoverHom {A B : Formula P} (f : Hom (normal A) (normal B)) : Presentation.Hom A B :=
  Presentation.comp (Presentation.NegationNormalization.forward A)
    (Presentation.comp (inclusion f) (Presentation.NegationNormalization.backward B))

theorem recoverHom_id (A : Formula P) : recoverHom (id (normal A)) = Presentation.id A := by
  rw [recoverHom,inclusion_id,Presentation.Laws.id_comp,
    Presentation.NegationNormalization.forward_backward]

theorem recoverHom_comp {A B C : Formula P}
    (f : Hom (normal A) (normal B)) (g : Hom (normal B) (normal C)) :
    recoverHom (comp f g) = Presentation.comp (recoverHom f) (recoverHom g) := by
  rw [recoverHom,inclusion_comp,recoverHom,recoverHom]
  simp only [Presentation.Laws.assoc]
  rw [← Presentation.Laws.assoc (Presentation.NegationNormalization.backward B)
      (Presentation.NegationNormalization.forward B),
    Presentation.NegationNormalization.backward_forward,Presentation.Laws.id_comp]

theorem recover_reduceHom {A B : Formula P} (f : Presentation.Hom A B) : recoverHom (reduceHom f) = f := by
  rw [recoverHom,inclusion_reduceHom]
  have h : Presentation.comp
      (Presentation.comp (Presentation.NegationNormalization.forward A) ((Presentation.normalization P).transport f))
      (Presentation.NegationNormalization.backward B) = f := (Presentation.normalization P).recover f
  simpa only [Presentation.Laws.assoc] using h

theorem reduce_recoverHom {A B : Formula P} (f : Hom (normal A) (normal B)) :
    reduceHom (recoverHom f) = f := by
  apply inclusion_injective
  rw [inclusion_reduceHom]
  change Presentation.comp
    (Presentation.comp (Presentation.NegationNormalization.backward A)
      (Presentation.comp (Presentation.NegationNormalization.forward A)
        (Presentation.comp (inclusion f) (Presentation.NegationNormalization.backward B))))
    (Presentation.NegationNormalization.forward B) = inclusion f
  simp only [← Presentation.Laws.assoc]
  rw [Presentation.NegationNormalization.backward_forward,Presentation.Laws.id_comp,
    Presentation.Laws.assoc,Presentation.NegationNormalization.backward_forward,Presentation.Laws.comp_id]

end DosenPetric.Reduced
