module

public import DosenPetric.GentzenRepresented

@[expose] public section
set_option autoImplicit false
namespace DosenPetric
universe u v
namespace DiagonalData
variable {O : Type u} {C : Category.{u,v} O} {M : MonoidalData C} (D : DiagonalData M)

theorem ext {X A B : O} (f g : C.Hom X (M.obj A B))
    (hf : C.comp f (D.fst A B) = C.comp g (D.fst A B))
    (hg : C.comp f (D.snd A B) = C.comp g (D.snd A B)) : f = g := by
  have h := D.pair_eta f
  rw [hf, hg] at h
  exact h.symm.trans (D.pair_eta g)

theorem pair_pre {W X A B : O} (h : C.Hom W X) (f : C.Hom X A) (g : C.Hom X B) :
    C.comp h (D.pair f g) = D.pair (C.comp h f) (C.comp h g) := by
  rw [pair, ← C.assoc, ← D.diag_nat, C.assoc, M.tensor_comp]
  rfl

theorem assocR_fst
    (hu : ∀ A B, C.comp (M.assocR A B M.unit) (M.rightOut (M.obj A B)) =
      M.tensor (C.id A) (M.rightOut B)) (A B E : O) :
    C.comp (M.assocR A B E) (D.fst (M.obj A B) E) = M.tensor (C.id A) (D.fst B E) := by
  rw [D.fst_formula (M.obj A B) E, ← C.assoc, ← M.tensor_id A B,
    M.assocR_nat, C.assoc, hu, M.tensor_comp, C.id_comp, ← D.fst_formula]

theorem assocR_snd (A B E : O) :
    C.comp (M.assocR A B E) (D.snd (M.obj A B) E) =
      C.comp (D.snd A (M.obj B E)) (D.snd B E) := by
  have h := congrArg (fun k => C.comp k (D.snd A E)) (D.fst_assoc A B E)
  rw [C.assoc, ← D.snd_nat, C.comp_id, ← D.snd_nat] at h
  exact h

theorem assocR_pair
    (hu : ∀ A B, C.comp (M.assocR A B M.unit) (M.rightOut (M.obj A B)) =
      M.tensor (C.id A) (M.rightOut B)) (A B E : O) :
    M.assocR A B E =
      D.pair (D.pair (D.fst A (M.obj B E)) (C.comp (D.snd A (M.obj B E)) (D.fst B E)))
        (C.comp (D.snd A (M.obj B E)) (D.snd B E)) := by
  apply D.ext
  · rw [D.assocR_fst hu, D.pair_fst]
    apply D.ext
    · rw [← D.fst_nat, C.comp_id, D.pair_fst]
    · rw [← D.snd_nat, D.pair_snd]
  · rw [D.assocR_snd, D.pair_snd]

theorem assocL_pair
    (hu : ∀ A B, C.comp (M.assocR A B M.unit) (M.rightOut (M.obj A B)) =
      M.tensor (C.id A) (M.rightOut B)) (A B E : O) :
    M.assocL A B E =
      D.pair (C.comp (D.fst (M.obj A B) E) (D.fst A B))
        (D.pair (C.comp (D.fst (M.obj A B) E) (D.snd A B)) (D.snd (M.obj A B) E)) := by
  apply cancel_left (C := C) _ _ (M.assocR A B E) (M.assocL A B E) (M.assocL_R A B E)
  rw [M.assocR_L, D.pair_pre, D.pair_pre]
  simp only [← C.assoc]
  rw [D.assocR_fst hu, D.assocR_snd, ← D.fst_nat, C.comp_id, ← D.snd_nat, D.pair_eta]
  have h := D.pair_eta (C.id (M.obj A (M.obj B E)))
  rw [C.id_comp, C.id_comp] at h
  exact h.symm

end DiagonalData
end DosenPetric
