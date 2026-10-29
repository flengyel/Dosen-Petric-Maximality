module

public import DosenPetric.ReducedDualInvolution

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}
open Presentation.NegationNormalization (normal form_true)

theorem castHom_trans {A B C D E F : NormalForm P}
    (hA : A = C) (hB : B = D) (hC : C = E) (hD : D = F) (f : Hom A B) :
    castHom hC hD (castHom hA hB f) = castHom (hA.trans hC) (hB.trans hD) f := by
  cases hA; cases hB; cases hC; cases hD; rfl

theorem castHom_tensor_conj {A B C D A' B' C' D' : NormalForm P}
    (hA : A = A') (hB : B = B') (hC : C = C') (hD : D = D')
    (f : Hom A C) (g : Hom B D) :
    castHom (congrArgTwo NormalForm.conj hA hB) (congrArgTwo NormalForm.conj hC hD)
      (tensor .conj f g) = tensor .conj (castHom hA hC f) (castHom hB hD g) := by
  cases hA; cases hB; cases hC; cases hD; rfl

theorem castHom_tensor_disj {A B C D A' B' C' D' : NormalForm P}
    (hA : A = A') (hB : B = B') (hC : C = C') (hD : D = D')
    (f : Hom A C) (g : Hom B D) :
    castHom (congrArgTwo NormalForm.disj hA hB) (congrArgTwo NormalForm.disj hC hD)
      (tensor .disj f g) = tensor .disj (castHom hA hC f) (castHom hB hD g) := by
  cases hA; cases hB; cases hC; cases hD; rfl

theorem reduce_negate {A B : Formula P} (f : Presentation.Hom A B) :
    reduceHom (Presentation.negate f) = negReduceHom f := reduce_recoverHom _

theorem negReduceHom_tensor_conj {A B C D : Formula P}
    (f : Presentation.Hom A C) (g : Presentation.Hom B D) :
    negReduceHom (Presentation.tensor .conj f g) =
      tensor .disj (negReduceHom f) (negReduceHom g) := by
  rw [negReduceHom,reduceHom_tensor_conj,dualHom_tensor_conj]
  exact castHom_tensor_disj (form_true C).symm (form_true D).symm
    (form_true A).symm (form_true B).symm _ _

theorem negReduceHom_tensor_disj {A B C D : Formula P}
    (f : Presentation.Hom A C) (g : Presentation.Hom B D) :
    negReduceHom (Presentation.tensor .disj f g) =
      tensor .conj (negReduceHom f) (negReduceHom g) := by
  rw [negReduceHom,reduceHom_tensor_disj,dualHom_tensor_disj]
  exact castHom_tensor_conj (form_true C).symm (form_true D).symm
    (form_true A).symm (form_true B).symm _ _

theorem negReduceHom_twice {A B : Formula P} (f : Presentation.Hom A B) :
    negReduceHom (Presentation.negate f) = reduceHom f := by
  rw [negReduceHom,reduce_negate,negReduceHom,dualHom_cast,castHom_trans]
  exact dualHom_involutive (reduceHom f)

end DosenPetric.Reduced
