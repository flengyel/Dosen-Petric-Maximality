module

public import DosenPetric.GentzenContextComponents

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem exchangeSide_nil_shuffle (o : Op) (X Y Δ : List (NormalForm P)) :
    exchangeSide o [] X Y Δ = (side P o).comp (split o (X ++ Y) Δ)
      ((side P o).comp ((sideM P o).tensor (shuffle o X Y) ((side P o).id (fold o Δ)))
        (join o (Y ++ X) Δ)) := exchangeSide_nil o X Y Δ

theorem exchangeSide_nil_Y (o : Op) (X Δ : List (NormalForm P))
    {Y : List (NormalForm P)} {A : NormalForm P} (a : At Y A) :
    (side P o).comp (exchangeSide o [] X Y Δ) (component o ((a.before X).before Δ)) =
      component o ((At.shift X a).before Δ) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  apply DiagonalData.cancel_left (C := C) _ _ (join o (X ++ Y) Δ) (split o (X ++ Y) Δ)
    (split_join o (X ++ Y) Δ)
  rw [exchangeSide_nil_shuffle]
  rw [← C.assoc, ← C.assoc, join_split, C.id_comp]
  rw [C.assoc, join_before, ← C.assoc, ← D.fst_nat, C.assoc, shuffle_Y, join_before]

theorem exchangeSide_nil_X (o : Op) (Y Δ : List (NormalForm P))
    {X : List (NormalForm P)} {A : NormalForm P} (a : At X A) :
    (side P o).comp (exchangeSide o [] X Y Δ) (component o ((At.shift Y a).before Δ)) =
      component o ((a.before Y).before Δ) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  apply DiagonalData.cancel_left (C := C) _ _ (join o (X ++ Y) Δ) (split o (X ++ Y) Δ)
    (split_join o (X ++ Y) Δ)
  rw [exchangeSide_nil_shuffle]
  rw [← C.assoc, ← C.assoc, join_split, C.id_comp]
  rw [C.assoc, join_before, ← C.assoc, ← D.fst_nat, C.assoc, shuffle_X, join_before]

theorem exchangeSide_nil_tail (o : Op) (X Y : List (NormalForm P))
    {Δ : List (NormalForm P)} {A : NormalForm P} (a : At Δ A) :
    (side P o).comp (exchangeSide o [] X Y Δ) (component o (At.shift (Y ++ X) a)) =
      component o (At.shift (X ++ Y) a) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  apply DiagonalData.cancel_left (C := C) _ _ (join o (X ++ Y) Δ) (split o (X ++ Y) Δ)
    (split_join o (X ++ Y) Δ)
  rw [exchangeSide_nil_shuffle]
  rw [← C.assoc, ← C.assoc, join_split, C.id_comp]
  rw [C.assoc, join_shift, ← C.assoc, ← D.snd_nat, C.comp_id, join_shift]

theorem exchangeSide_prefix (o : Op) {Γ : List (NormalForm P)}
    (X Y Δ : List (NormalForm P)) {A : NormalForm P} (a : At Γ A) :
    (side P o).comp (exchangeSide o Γ X Y Δ) (component o (((a.before Y).before X).before Δ)) =
      component o (((a.before X).before Y).before Δ) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  let q := o
  cases o <;> induction a with
  | here A Γ =>
    simp only [At.before]
    rw [exchangeSide_cons, component_here, ← D.fst_nat, C.comp_id, component_here]
  | @there A B Γ a ih =>
    simp only [At.before]
    rw [exchangeSide_cons, component_there, component_there, ← C.assoc,
      ← D.snd_nat, C.assoc, ih]
    rfl

theorem exchangeSide_X (o : Op) (Γ X Y Δ : List (NormalForm P))
    {A : NormalForm P} (a : At X A) :
    (side P o).comp (exchangeSide o Γ X Y Δ) (component o ((At.shift (Γ ++ Y) a).before Δ)) =
      component o (((At.shift Γ a).before Y).before Δ) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  cases o <;> induction Γ with
  | nil => exact exchangeSide_nil_X _ _ _ a
  | cons B Γ ih =>
    simp only [List.cons_append, At.shift, At.before]
    rw [exchangeSide_cons, component_there, component_there, ← C.assoc,
      ← D.snd_nat, C.assoc, ih]
    rfl

theorem exchangeSide_Y (o : Op) (Γ X Y Δ : List (NormalForm P))
    {A : NormalForm P} (a : At Y A) :
    (side P o).comp (exchangeSide o Γ X Y Δ) (component o (((At.shift Γ a).before X).before Δ)) =
      component o ((At.shift (Γ ++ X) a).before Δ) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  cases o <;> induction Γ with
  | nil => exact exchangeSide_nil_Y _ _ _ a
  | cons B Γ ih =>
    simp only [List.cons_append, At.shift, At.before]
    rw [exchangeSide_cons, component_there, component_there, ← C.assoc,
      ← D.snd_nat, C.assoc, ih]
    rfl

theorem exchangeSide_tail (o : Op) (Γ X Y Δ : List (NormalForm P))
    {A : NormalForm P} (a : At Δ A) :
    (side P o).comp (exchangeSide o Γ X Y Δ) (component o (At.shift (Γ ++ Y ++ X) a)) =
      component o (At.shift (Γ ++ X ++ Y) a) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  cases o <;> induction Γ with
  | nil => exact exchangeSide_nil_tail _ _ _ a
  | cons B Γ ih =>
    simp only [List.cons_append, At.shift]
    rw [exchangeSide_cons, component_there, component_there, ← C.assoc,
      ← D.snd_nat, C.assoc, ih]
    rfl

end DosenPetric.Reduced.Gentzen
