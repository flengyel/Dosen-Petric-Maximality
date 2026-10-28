module

public import DosenPetric.GentzenMirrorInterpretation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem cross_first (o : Op) (A B T : NormalForm P) :
    (side P o).comp ((sideM P o).cross A B T) ((sideD P o).fst B (o.formula A T)) =
      (side P o).comp ((sideD P o).snd A (o.formula B T)) ((sideD P o).fst B T) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  change C.comp (C.comp (M.assocR A B T)
    (C.comp (M.tensor (M.swap A B) (C.id T)) (M.assocL B A T))) _ = _
  rw [C.assoc, C.assoc]
  rw [logical_head_first o B A T, ← C.assoc (M.tensor (M.swap A B) (C.id T)),
    ← D.fst_nat, C.assoc, ← D.snd_swap]
  rw [← C.assoc, D.assocR_fst (side_unit o), ← D.snd_nat]

theorem cross_second (o : Op) (A B T : NormalForm P) :
    (side P o).comp ((sideM P o).cross A B T)
        ((side P o).comp ((sideD P o).snd B (o.formula A T)) ((sideD P o).fst A T)) =
      (sideD P o).fst A (o.formula B T) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  change C.comp (C.comp (M.assocR A B T)
    (C.comp (M.tensor (M.swap A B) (C.id T)) (M.assocL B A T))) _ = _
  rw [C.assoc, C.assoc]
  rw [logical_head_second o B A T, ← C.assoc (M.tensor (M.swap A B) (C.id T)),
    ← D.fst_nat, C.assoc, side_swap_snd]
  rw [← C.assoc, D.assocR_fst (side_unit o), ← D.fst_nat, C.comp_id]

theorem cross_tail (o : Op) (A B T : NormalForm P) :
    (side P o).comp ((sideM P o).cross A B T)
        ((side P o).comp ((sideD P o).snd B (o.formula A T)) ((sideD P o).snd A T)) =
      (side P o).comp ((sideD P o).snd A (o.formula B T)) ((sideD P o).snd B T) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  change C.comp (C.comp (M.assocR A B T)
    (C.comp (M.tensor (M.swap A B) (C.id T)) (M.assocL B A T))) _ = _
  rw [C.assoc, C.assoc]
  rw [logical_head_tail o B A T, ← D.snd_nat, C.comp_id, D.assocR_snd]

end DosenPetric.Reduced.Gentzen
