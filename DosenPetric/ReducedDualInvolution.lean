module

public import DosenPetric.PresentationNegationFunctor

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.NormalForm
universe u
variable {P : Type u}

def castOcc {A B : NormalForm P} (h : A = B) (x : A.formula.Occ) : B.formula.Occ := h ▸ x

theorem castOcc_conj_left {A B C D : NormalForm P} (hA : A = C) (hB : B = D) (x : A.formula.Occ) :
    castOcc (congrArgTwo NormalForm.conj hA hB) (Sum.inl x) = Sum.inl (castOcc hA x) := by
  cases hA
  cases hB
  rfl

theorem castOcc_conj_right {A B C D : NormalForm P} (hA : A = C) (hB : B = D) (x : B.formula.Occ) :
    castOcc (congrArgTwo NormalForm.conj hA hB) (Sum.inr x) = Sum.inr (castOcc hB x) := by
  cases hA
  cases hB
  rfl

theorem castOcc_disj_left {A B C D : NormalForm P} (hA : A = C) (hB : B = D) (x : A.formula.Occ) :
    castOcc (congrArgTwo NormalForm.disj hA hB) (Sum.inl x) = Sum.inl (castOcc hA x) := by
  cases hA
  cases hB
  rfl

theorem castOcc_disj_right {A B C D : NormalForm P} (hA : A = C) (hB : B = D) (x : B.formula.Occ) :
    castOcc (congrArgTwo NormalForm.disj hA hB) (Sum.inr x) = Sum.inr (castOcc hB x) := by
  cases hA
  cases hB
  rfl

theorem toDual_twice (A : NormalForm P) (x : A.formula.Occ) :
    castOcc (dual_dual A) (toDual A.dual (toDual A x)) = x := by
  induction A with
  | lit l => cases l <;> rfl
  | top => cases x
  | bot => cases x
  | conj A B ih ih' =>
    cases x with
    | inl x =>
      change castOcc (congrArgTwo NormalForm.conj (dual_dual A) (dual_dual B))
        (Sum.inl (toDual A.dual (toDual A x))) = Sum.inl x
      rw [castOcc_conj_left (dual_dual A) (dual_dual B),ih]
    | inr x =>
      change castOcc (congrArgTwo NormalForm.conj (dual_dual A) (dual_dual B))
        (Sum.inr (toDual B.dual (toDual B x))) = Sum.inr x
      rw [castOcc_conj_right (dual_dual A) (dual_dual B),ih']
  | disj A B ih ih' =>
    cases x with
    | inl x =>
      change castOcc (congrArgTwo NormalForm.disj (dual_dual A) (dual_dual B))
        (Sum.inl (toDual A.dual (toDual A x))) = Sum.inl x
      rw [castOcc_disj_left (dual_dual A) (dual_dual B),ih]
    | inr x =>
      change castOcc (congrArgTwo NormalForm.disj (dual_dual A) (dual_dual B))
        (Sum.inr (toDual B.dual (toDual B x))) = Sum.inr x
      rw [castOcc_disj_right (dual_dual A) (dual_dual B),ih']

end DosenPetric.NormalForm
namespace DosenPetric.Reduced
universe u
variable {P : Type u}

theorem occurrence_castHom {A B C D : NormalForm P} (hA : A = C) (hB : B = D)
    (f : Hom A B) (x : A.formula.Occ) (y : B.formula.Occ) :
    occurrenceMap (castHom hA hB f) (NormalForm.castOcc hA x) (NormalForm.castOcc hB y) ↔
      occurrenceMap f x y := by
  cases hA
  cases hB
  rfl

theorem dualHom_cast {A B C D : NormalForm P} (hA : A = C) (hB : B = D) (f : Hom A B) :
    dualHom (castHom hA hB f) =
      castHom (congrArg NormalForm.dual hB) (congrArg NormalForm.dual hA) (dualHom f) := by
  cases hA
  cases hB
  rfl

theorem dualHom_involutive {A B : NormalForm P} (f : Hom A B) :
    castHom (NormalForm.dual_dual A) (NormalForm.dual_dual B) (dualHom (dualHom f)) = f := by
  apply faithful
  funext x y
  apply propext
  have hc := occurrence_castHom (NormalForm.dual_dual A) (NormalForm.dual_dual B)
    (dualHom (dualHom f)) (NormalForm.toDual A.dual (NormalForm.toDual A x))
    (NormalForm.toDual B.dual (NormalForm.toDual B y))
  rw [NormalForm.toDual_twice,NormalForm.toDual_twice] at hc
  exact hc.trans ((dualHom_relation (dualHom f) (NormalForm.toDual B y) (NormalForm.toDual A x)).trans
    (dualHom_relation f x y))

theorem dualHom_tensor_conj {A B C D : NormalForm P} (f : Hom A C) (g : Hom B D) :
    dualHom (tensor .conj f g) = tensor .disj (dualHom f) (dualHom g) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

theorem dualHom_tensor_disj {A B C D : NormalForm P} (f : Hom A C) (g : Hom B D) :
    dualHom (tensor .disj f g) = tensor .conj (dualHom f) (dualHom g) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

end DosenPetric.Reduced
