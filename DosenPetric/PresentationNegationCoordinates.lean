module

public import DosenPetric.PresentationMaximality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.NormalForm
universe u
variable {P : Type u}

theorem castOcc_trans {A B C : NormalForm P} (h : A = B) (k : B = C) (x : A.formula.Occ) :
    castOcc k (castOcc h x) = castOcc (h.trans k) x := by
  cases h; cases k; rfl

theorem castOcc_injective {A B : NormalForm P} (h : A = B) {x y : A.formula.Occ}
    (he : castOcc h x = castOcc h y) : x = y := by
  cases h; exact he

theorem toDual_cast {A B : NormalForm P} (h : A = B) (x : A.formula.Occ) :
    toDual B (castOcc h x) = castOcc (congrArg NormalForm.dual h) (toDual A x) := by
  cases h; rfl

end DosenPetric.NormalForm
namespace DosenPetric.Presentation.NegationNormalization
universe u
variable {P : Type u}
open NormalForm (castOcc)

/-- Normalization and literal duality keep the same original occurrence tags. -/
theorem toOcc_neg (A : Formula P) (x : A.Occ) :
    castOcc (form_true A) (toOcc (.neg A) x) = NormalForm.toDual (normal A) (toOcc A x) := by
  induction A with
  | var p => rfl
  | top => cases x
  | bot => cases x
  | conj A B ih ih' =>
    cases x with
    | inl x =>
      change castOcc (congrArgTwo NormalForm.disj (form_true A) (form_true B))
        (Sum.inl (toOcc (.neg A) x)) = Sum.inl (NormalForm.toDual (normal A) (toOcc A x))
      rw [NormalForm.castOcc_disj_left (form_true A) (form_true B),ih]
    | inr x =>
      change castOcc (congrArgTwo NormalForm.disj (form_true A) (form_true B))
        (Sum.inr (toOcc (.neg B) x)) = Sum.inr (NormalForm.toDual (normal B) (toOcc B x))
      rw [NormalForm.castOcc_disj_right (form_true A) (form_true B),ih']
  | disj A B ih ih' =>
    cases x with
    | inl x =>
      change castOcc (congrArgTwo NormalForm.conj (form_true A) (form_true B))
        (Sum.inl (toOcc (.neg A) x)) = Sum.inl (NormalForm.toDual (normal A) (toOcc A x))
      rw [NormalForm.castOcc_conj_left (form_true A) (form_true B),ih]
    | inr x =>
      change castOcc (congrArgTwo NormalForm.conj (form_true A) (form_true B))
        (Sum.inr (toOcc (.neg B) x)) = Sum.inr (NormalForm.toDual (normal B) (toOcc B x))
      rw [NormalForm.castOcc_conj_right (form_true A) (form_true B),ih']
  | neg A ih =>
    have ht := congrArg (NormalForm.toDual (normal A).dual) (ih x)
    erw [NormalForm.toDual_cast (form_true A)] at ht
    have hh := congrArg (castOcc (NormalForm.dual_dual (normal A))) ht
    rw [NormalForm.castOcc_trans,NormalForm.toDual_twice] at hh
    apply NormalForm.castOcc_injective ((congrArg NormalForm.dual (form_true A)).trans
      (NormalForm.dual_dual (normal A)))
    rw [NormalForm.castOcc_trans]
    exact hh.symm

end DosenPetric.Presentation.NegationNormalization
