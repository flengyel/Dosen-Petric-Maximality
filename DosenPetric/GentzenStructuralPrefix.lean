module

public import DosenPetric.GentzenCutSplice

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace StructuralProgram
variable {F U : List (NormalForm P)}

def prefixFixed (p : StructuralProgram P F U) (Γ : List (NormalForm P)) :
    StructuralProgram P (Γ ++ F) (Γ ++ U) :=
  match Γ with
  | [] => p
  | A :: Γ => (p.prefixFixed Γ).consFixed A

theorem prefixFixed_before (p : StructuralProgram P F U) {Γ : List (NormalForm P)}
    {A : NormalForm P} (a : At Γ A) : (p.prefixFixed Γ).get (a.before U) = a.before F := by
  induction a with
  | here => exact consFixed_here _ _
  | there a ih => exact (consFixed_there _ _ _).trans (congrArg At.there ih)

theorem prefixFixed_shift (p : StructuralProgram P F U) (Γ : List (NormalForm P))
    {A : NormalForm P} (a : At U A) :
    (p.prefixFixed Γ).get (At.shift Γ a) = At.shift Γ (p.get a) := by
  induction Γ with
  | nil => rfl
  | cons B Γ ih => exact (consFixed_there B _ _).trans (congrArg At.there ih)

theorem prefixFixed_atomic (p : StructuralProgram P F U) (Γ : List (NormalForm P))
    (hp : p.Atomic) : (p.prefixFixed Γ).Atomic := by
  induction Γ with
  | nil => exact hp
  | cons A Γ ih => exact atomic_consFixed _ A ih

theorem prefixFixed_join (p : StructuralProgram P F U) (o : Op) (Γ : List (NormalForm P)) :
    (side P o).comp (join o Γ F) ((p.prefixFixed Γ).arrow o) =
      (side P o).comp ((sideM P o).tensor ((side P o).id (fold o Γ)) (p.arrow o))
        (join o Γ U) := by
  let C := side P o
  let D := sideD P o
  apply side_ext o
  intro A a
  cases At.cases_append Γ U a with
  | inl h =>
    obtain ⟨a,rfl⟩ := h
    rw [C.assoc, component, prefixFixed_before, join_before,
      C.assoc, join_before, ← C.assoc, ← D.fst_nat, C.comp_id]
  | inr h =>
    obtain ⟨a,rfl⟩ := h
    rw [C.assoc, component, prefixFixed_shift, join_shift,
      C.assoc, join_shift, ← C.assoc, ← D.snd_nat, C.assoc, component]

theorem prefixFixed_split (p : StructuralProgram P F U) (o : Op) (Γ : List (NormalForm P)) :
    (side P o).comp ((p.prefixFixed Γ).arrow o) (split o Γ U) =
      (side P o).comp (split o Γ F)
        ((sideM P o).tensor ((side P o).id (fold o Γ)) (p.arrow o)) := by
  let C := side P o
  apply DiagonalData.cancel_left (C := C) _ _ (join o Γ F) (split o Γ F) (split_join o Γ F)
  rw [← C.assoc, prefixFixed_join, C.assoc, join_split, C.comp_id,
    ← C.assoc, join_split, C.id_comp]

end StructuralProgram
end DosenPetric.Reduced.Gentzen
