module

public import DosenPetric.GentzenHeadRouting

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric
universe u v
namespace DiagonalData
variable {O : Type u} {C : Category.{u,v} O} {M : MonoidalData C} (D : DiagonalData M)
variable (hu : ∀ A B, C.comp (M.assocR A B M.unit) (M.rightOut (M.obj A B)) =
  M.tensor (C.id A) (M.rightOut B))
variable (hs : ∀ A B, C.comp (M.swap A B) (D.snd B A) = D.fst A B)

theorem tensor_pair {A B E F : O} (f : C.Hom A E) (g : C.Hom B F) :
    M.tensor f g = D.pair (C.comp (D.fst A B) f) (C.comp (D.snd A B) g) := by
  apply D.ext
  · rw [D.pair_fst, ← D.fst_nat]
  · rw [D.pair_snd, ← D.snd_nat]

include hs in
theorem swap_pair (A B : O) : M.swap A B = D.pair (D.snd A B) (D.fst A B) := by
  apply D.ext
  · rw [D.pair_fst, ← D.snd_swap]
  · rw [D.pair_snd, hs]

theorem pair_fst_comp {X A B E : O} (f : C.Hom X A) (g : C.Hom X B) (h : C.Hom A E) :
    C.comp (D.pair f g) (C.comp (D.fst A B) h) = C.comp f h := by
  rw [← C.assoc, D.pair_fst]

theorem pair_snd_comp {X A B E : O} (f : C.Hom X A) (g : C.Hom X B) (h : C.Hom B E) :
    C.comp (D.pair f g) (C.comp (D.snd A B) h) = C.comp g h := by
  rw [← C.assoc, D.pair_snd]

include hu hs in
/-- The structural adapter before the outer dual component cut. -/
theorem dual_outer_route (X A T : O) :
    C.comp (M.swap A (M.obj X T))
      (C.comp (M.assocL X T A)
        (M.tensor (C.id X) (M.swap T A))) =
      M.cross A X T := by
  change C.comp (M.swap A (M.obj X T))
    (C.comp (M.assocL X T A) (M.tensor (C.id X) (M.swap T A))) =
      C.comp (M.assocR A X T) (C.comp (M.tensor (M.swap A X) (C.id T)) (M.assocL X A T))
  simp only [D.assocR_pair hu, D.assocL_pair hu, D.swap_pair hs, D.tensor_pair, D.pair_pre,
    D.pair_fst, D.pair_snd, D.pair_fst_comp, D.pair_snd_comp, C.comp_id]

include hu hs in
/-- The structural adapter before the inner dual component cut. -/
theorem dual_inner_route (A B T : O) :
    C.comp (M.swap B (M.obj T A))
      (C.comp (M.assocL T A B)
        (C.comp (M.swap T (M.obj A B)) (M.assocL A B T))) =
      C.comp (M.tensor (C.id B) (M.swap T A))
        (M.cross B A T) := by
  change C.comp (M.swap B (M.obj T A))
    (C.comp (M.assocL T A B) (C.comp (M.swap T (M.obj A B)) (M.assocL A B T))) =
      C.comp (M.tensor (C.id B) (M.swap T A))
        (C.comp (M.assocR B A T) (C.comp (M.tensor (M.swap B A) (C.id T)) (M.assocL A B T)))
  simp only [D.assocR_pair hu, D.assocL_pair hu, D.swap_pair hs, D.tensor_pair, D.pair_pre,
    D.pair_fst, D.pair_snd, D.pair_fst_comp, D.pair_snd_comp, C.comp_id]

end DiagonalData
end DosenPetric
