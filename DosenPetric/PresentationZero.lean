module

public import DosenPetric.PresentationStructure

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.Presentation

universe u

variable {P : Type u}

theorem zero_bot : zero (Formula.bot : Formula P) = id .bot :=
  ((operations P).fromBot_unique (zero .bot)).trans ((operations P).fromBot_unique (id .bot)).symm

/-- Existing arrows into bottom are equal, by initiality and the zero-identity law. -/
theorem toBot_unique {A : Formula P} (f g : Hom A .bot) : f = g := by
  have hf := Laws.zero_law f f
  have hg := Laws.zero_law f g
  rw [zero_bot, Laws.comp_id] at hf hg
  exact hf.symm.trans hg

theorem zeroConstruction_def (A : Formula P) : zeroConstruction A =
    comp (rightIn .conj A)
      (comp (tensor .conj (id A) (excludedMiddle A))
        (comp (dist A (.neg A) A)
          (comp (tensor .disj (contradiction A) (id A)) (leftOut .disj A)))) := rfl

private theorem comp_square {A B C D E F : Formula P}
    {a : Hom A B} {b : Hom B C} {r : Hom C F} {l : Hom A D}
    {a' : Hom D E} {b' : Hom E F} {m : Hom B E}
    (ha : comp a m = comp l a') (hb : comp b r = comp m b') :
    comp (comp a b) r = comp l (comp a' b') := by
  rw [Laws.assoc, hb, ← Laws.assoc, ha, Laws.assoc]

/-- Equation (0ηε), p.317, derived in the original equation-generated quotient. -/
theorem zeroConstruction_eq (A : Formula P) : zeroConstruction A = zero A := by
  have he : contradiction A = comp (tensor .conj (zero A) (id (.neg A))) (contradiction A) :=
    toBot_unique _ _
  have hu := Laws.rightIn_nat .conj (zero A)
  have ht :
      comp (tensor .conj (id A) (excludedMiddle A))
        (tensor .conj (zero A) (id (.disj (.neg A) A))) =
      comp (tensor .conj (zero A) (id .top))
        (tensor .conj (id A) (excludedMiddle A)) := by
    rw [Laws.tensor_comp, Laws.tensor_comp, Laws.id_comp, Laws.comp_id,
      Laws.comp_id, Laws.id_comp]
  have hd := Laws.dist_nat (zero A) (id (.neg A)) (id A)
  rw [Laws.tensor_id] at hd
  have hv : comp (tensor .disj (contradiction A) (id A)) (id (.disj .bot A)) =
      comp (tensor .disj (tensor .conj (zero A) (id (.neg A))) (id A))
        (tensor .disj (contradiction A) (id A)) := by
    rw [Laws.comp_id, Laws.tensor_comp, ← he, Laws.id_comp]
  have h := comp_square hu
    (comp_square ht
      (comp_square hd
        (comp_square hv
          ((Laws.comp_id (leftOut .disj A)).trans
            (Laws.id_comp (leftOut .disj A)).symm))))
  change comp (zeroConstruction A) (id A) = comp (zero A) (zeroConstruction A) at h
  rw [Laws.comp_id] at h
  have absorb := Laws.zero_law (zeroConstruction A) (id A)
  rw [Laws.id_comp] at absorb
  exact h.trans absorb

/-- The required interface uses the source construction, whose zero law is derived. -/
def zeroIdentity (P : Type u) : ZeroIdentity (category P) where
  zero := zeroConstruction
  law f g := by
    change comp (zeroConstruction _) f = comp g (zeroConstruction _)
    rw [zeroConstruction_eq, zeroConstruction_eq]
    exact Laws.zero_law f g

end DosenPetric.Presentation
