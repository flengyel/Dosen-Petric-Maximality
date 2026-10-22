module

public import DosenPetric.Category

@[expose] public section

set_option autoImplicit false

namespace DosenPetric

universe u v

def opposite {Obj : Type u} (C : Category.{u,v} Obj) : Category Obj where
  Hom A B := C.Hom B A
  id := C.id
  comp f g := C.comp g f
  id_comp := C.comp_id
  comp_id := C.id_comp
  assoc f g h := (C.assoc h g f).symm

/-- The monoidal laws needed below, all among the published primitive laws. -/
structure MonoidalData {Obj : Type u} (C : Category.{u,v} Obj) where
  obj : Obj → Obj → Obj
  unit : Obj
  tensor : {A B D E : Obj} → C.Hom A D → C.Hom B E → C.Hom (obj A B) (obj D E)
  tensor_id : ∀ A B, tensor (C.id A) (C.id B) = C.id (obj A B)
  tensor_comp : ∀ {A B D E F H} (f : C.Hom A D) (g : C.Hom B E)
    (h : C.Hom D F) (k : C.Hom E H),
    C.comp (tensor f g) (tensor h k) = tensor (C.comp f h) (C.comp g k)
  assocR : ∀ A B D, C.Hom (obj A (obj B D)) (obj (obj A B) D)
  assocL : ∀ A B D, C.Hom (obj (obj A B) D) (obj A (obj B D))
  assocR_L : ∀ A B D, C.comp (assocR A B D) (assocL A B D) = C.id (obj A (obj B D))
  assocL_R : ∀ A B D, C.comp (assocL A B D) (assocR A B D) = C.id (obj (obj A B) D)
  assocR_nat : ∀ {A B D E F H} (f : C.Hom A E) (g : C.Hom B F) (h : C.Hom D H),
    C.comp (assocR A B D) (tensor (tensor f g) h) = C.comp (tensor f (tensor g h)) (assocR E F H)
  assocL_nat : ∀ {A B D E F H} (f : C.Hom A E) (g : C.Hom B F) (h : C.Hom D H),
    C.comp (assocL A B D) (tensor f (tensor g h)) = C.comp (tensor (tensor f g) h) (assocL E F H)
  swap : ∀ A B, C.Hom (obj A B) (obj B A)
  swap_nat : ∀ {A B D E} (f : C.Hom A D) (g : C.Hom B E),
    C.comp (swap A B) (tensor g f) = C.comp (tensor f g) (swap D E)
  rightOut : ∀ A, C.Hom (obj A unit) A
  rightIn : ∀ A, C.Hom A (obj A unit)
  leftOut : ∀ A, C.Hom (obj unit A) A
  leftIn : ∀ A, C.Hom A (obj unit A)
  rightOut_In : ∀ A, C.comp (rightOut A) (rightIn A) = C.id (obj A unit)
  rightIn_Out : ∀ A, C.comp (rightIn A) (rightOut A) = C.id A
  leftOut_In : ∀ A, C.comp (leftOut A) (leftIn A) = C.id (obj unit A)
  leftIn_Out : ∀ A, C.comp (leftIn A) (leftOut A) = C.id A
  rightIn_nat : ∀ {A D} (f : C.Hom A D),
    C.comp (rightIn A) (tensor f (C.id unit)) = C.comp f (rightIn D)
  leftOut_nat : ∀ {A D} (f : C.Hom A D),
    C.comp (leftOut A) f = C.comp (tensor (C.id unit) f) (leftOut D)
  triangle : ∀ A D, assocR A unit D =
    C.comp (tensor (C.id A) (leftOut D)) (tensor (rightIn A) (C.id D))

namespace MonoidalData

variable {Obj : Type u} {C : Category.{u,v} Obj} (M : MonoidalData C)

def cross (A B D : Obj) : C.Hom (M.obj A (M.obj B D)) (M.obj B (M.obj A D)) :=
  C.comp (M.assocR A B D) (C.comp (M.tensor (M.swap A B) (C.id D)) (M.assocL B A D))

def medial (A B D E : Obj) : C.Hom (M.obj (M.obj A B) (M.obj D E))
    (M.obj (M.obj A D) (M.obj B E)) :=
  C.comp (M.assocL A B (M.obj D E))
    (C.comp (M.tensor (C.id A) (M.cross B D E)) (M.assocR A D (M.obj B E)))

theorem square_comp {A B D A' B' D' : Obj} {a : C.Hom A B} {b : C.Hom B D}
    {a' : C.Hom A' B'} {b' : C.Hom B' D'}
    {l : C.Hom A A'} {m : C.Hom B B'} {r : C.Hom D D'}
    (ha : C.comp a m = C.comp l a') (hb : C.comp b r = C.comp m b') :
    C.comp (C.comp a b) r = C.comp l (C.comp a' b') := by
  rw [C.assoc, hb, ← C.assoc, ha, C.assoc]

theorem tensor_square {A B D E A' B' D' E' : Obj}
    {a : C.Hom A B} {b : C.Hom D E} {a' : C.Hom A' B'} {b' : C.Hom D' E'}
    {l : C.Hom A A'} {r : C.Hom B B'} {l' : C.Hom D D'} {r' : C.Hom E E'}
    (ha : C.comp a r = C.comp l a') (hb : C.comp b r' = C.comp l' b') :
    C.comp (M.tensor a b) (M.tensor r r') = C.comp (M.tensor l l') (M.tensor a' b') := by
  rw [M.tensor_comp, M.tensor_comp, ha, hb]

theorem id_square {A B : Obj} (f : C.Hom A B) : C.comp (C.id A) f = C.comp f (C.id B) := by
  rw [C.id_comp, C.comp_id]

theorem cross_nat {A B D E F H : Obj} (f : C.Hom A E) (g : C.Hom B F) (h : C.Hom D H) :
    C.comp (M.cross A B D) (M.tensor g (M.tensor f h)) =
      C.comp (M.tensor f (M.tensor g h)) (M.cross E F H) := by
  exact square_comp (M.assocR_nat f g h)
    (square_comp (M.tensor_square (M.swap_nat f g) (id_square h)) (M.assocL_nat g f h))

theorem medial_nat {A B D E A' B' D' E' : Obj}
    (f : C.Hom A A') (g : C.Hom B B') (h : C.Hom D D') (k : C.Hom E E') :
    C.comp (M.medial A B D E) (M.tensor (M.tensor f h) (M.tensor g k)) =
      C.comp (M.tensor (M.tensor f g) (M.tensor h k)) (M.medial A' B' D' E') := by
  exact square_comp (M.assocL_nat f g (M.tensor h k))
    (square_comp (M.tensor_square (id_square f) (M.cross_nat g h k))
      (M.assocR_nat f h (M.tensor g k)))

end MonoidalData

/-- The diagonal/projection equations of §9.1, without product eta as an input. -/
structure DiagonalData {Obj : Type u} {C : Category.{u,v} Obj} (M : MonoidalData C) where
  diag : ∀ A, C.Hom A (M.obj A A)
  fst : ∀ A B, C.Hom (M.obj A B) A
  snd : ∀ A B, C.Hom (M.obj A B) B
  diag_nat : ∀ {A B} (f : C.Hom A B),
    C.comp (diag A) (M.tensor f f) = C.comp f (diag B)
  fst_nat : ∀ {A B D E} (f : C.Hom A D) (g : C.Hom B E),
    C.comp (fst A B) f = C.comp (M.tensor f g) (fst D E)
  snd_nat : ∀ {A B D E} (f : C.Hom A D) (g : C.Hom B E),
    C.comp (snd A B) g = C.comp (M.tensor f g) (snd D E)
  diag_fst : ∀ A, C.comp (diag A) (fst A A) = C.id A
  diag_snd : ∀ A, C.comp (diag A) (snd A A) = C.id A
  snd_swap : ∀ A B, snd A B = C.comp (M.swap A B) (fst B A)
  fst_unit : ∀ A, fst A M.unit = M.rightOut A
  fst_assoc : ∀ A B D, C.comp (M.assocR A B D) (M.tensor (fst A B) (C.id D)) =
    M.tensor (C.id A) (snd B D)
  diag_tensor : ∀ A B, diag (M.obj A B) =
    C.comp (M.tensor (diag A) (diag B)) (M.medial A A B B)

namespace DiagonalData

variable {Obj : Type u} {C : Category.{u,v} Obj} {M : MonoidalData C} (D : DiagonalData M)

theorem cancel_right {X A B : Obj} (f g : C.Hom X A) (r : C.Hom A B) (s : C.Hom B A)
    (hrs : C.comp r s = C.id A) (h : C.comp f r = C.comp g r) : f = g := by
  have hh := congrArg (fun k => C.comp k s) h
  rw [C.assoc, C.assoc, hrs, C.comp_id, C.comp_id] at hh
  exact hh

theorem cancel_left {A B X : Obj} (f g : C.Hom A X) (r : C.Hom B A) (s : C.Hom A B)
    (hsr : C.comp s r = C.id A) (h : C.comp r f = C.comp r g) : f = g := by
  have hh := congrArg (fun k => C.comp s k) h
  rw [← C.assoc, ← C.assoc, hsr, C.id_comp, C.id_comp] at hh
  exact hh

def toUnit (A : Obj) : C.Hom A M.unit := C.comp (M.rightIn A) (D.snd A M.unit)

include D

theorem diag_unit : D.diag M.unit = M.rightIn M.unit := by
  apply cancel_right _ _ (M.rightOut M.unit) (M.rightIn M.unit) (M.rightOut_In M.unit)
  rw [← D.fst_unit, D.diag_fst, D.fst_unit, M.rightIn_Out]

theorem toUnit_unit : D.toUnit M.unit = C.id M.unit := by
  unfold toUnit
  rw [← D.diag_unit, D.diag_snd]

theorem toUnit_nat {A B : Obj} (f : C.Hom A B) : C.comp f (D.toUnit B) = D.toUnit A := by
  unfold toUnit
  rw [← C.assoc, ← M.rightIn_nat, C.assoc, ← D.snd_nat, C.comp_id]

theorem toUnit_unique {A : Obj} (f : C.Hom A M.unit) : f = D.toUnit A := by
  have h := D.toUnit_nat f
  rw [D.toUnit_unit, C.comp_id] at h
  exact h

omit D in
theorem tensor_unit_faithful {A B : Obj} (f g : C.Hom A B)
    (h : M.tensor (C.id M.unit) f = M.tensor (C.id M.unit) g) : f = g := by
  apply cancel_left _ _ (M.leftOut A) (M.leftIn A) (M.leftIn_Out A)
  rw [M.leftOut_nat, M.leftOut_nat, h]

theorem snd_unit (A : Obj) : D.snd M.unit A = M.leftOut A := by
  apply tensor_unit_faithful
  have h := D.fst_assoc M.unit M.unit A
  rw [D.fst_unit, M.triangle, C.assoc, M.tensor_comp,
    M.rightIn_Out, C.comp_id, M.tensor_id, C.comp_id] at h
  exact h.symm

theorem fst_formula (A B : Obj) :
    D.fst A B = C.comp (M.tensor (C.id A) (D.toUnit B)) (M.rightOut A) := by
  have h := D.fst_nat (C.id A) (D.toUnit B)
  rw [C.comp_id, D.fst_unit] at h
  exact h

theorem snd_formula (A B : Obj) :
    D.snd A B = C.comp (M.tensor (D.toUnit A) (C.id B)) (M.leftOut B) := by
  have h := D.snd_nat (D.toUnit A) (C.id B)
  rw [C.comp_id, D.snd_unit] at h
  exact h

theorem diag_right (A : Obj) :
    C.comp (D.diag A) (M.tensor (C.id A) (D.toUnit A)) = M.rightIn A := by
  apply cancel_right _ _ (M.rightOut A) (M.rightIn A) (M.rightOut_In A)
  rw [C.assoc, ← D.fst_formula, D.diag_fst, M.rightIn_Out]

theorem diag_left (A : Obj) :
    C.comp (D.diag A) (M.tensor (D.toUnit A) (C.id A)) = M.leftIn A := by
  apply cancel_right _ _ (M.leftOut A) (M.leftIn A) (M.leftOut_In A)
  rw [C.assoc, ← D.snd_formula, D.diag_snd, M.leftIn_Out]

theorem swap_unit : M.swap M.unit M.unit = C.id (M.obj M.unit M.unit) := by
  apply cancel_right _ _ (M.rightOut M.unit) (M.rightIn M.unit) (M.rightOut_In M.unit)
  rw [← D.fst_unit, ← D.snd_swap, C.id_comp]
  exact (D.toUnit_unique _).trans (D.toUnit_unique _).symm

theorem medial_unit (A B : Obj) :
    M.medial A M.unit M.unit B = C.id (M.obj (M.obj A M.unit) (M.obj M.unit B)) := by
  unfold MonoidalData.medial MonoidalData.cross
  rw [D.swap_unit, M.tensor_id, C.id_comp, M.assocR_L, M.tensor_id, C.id_comp, M.assocL_R]

/-- (w k k), p.187, derived from diagonal compatibility, units, and projections. -/
theorem diag_projections (A B : Obj) :
    C.comp (D.diag (M.obj A B)) (M.tensor (D.fst A B) (D.snd A B)) = C.id (M.obj A B) := by
  rw [D.diag_tensor, D.fst_formula, D.snd_formula, ← M.tensor_comp]
  simp only [C.assoc]
  rw [← C.assoc (M.medial A A B B), M.medial_nat]
  rw [C.assoc, D.medial_unit, C.id_comp, ← C.assoc, M.tensor_comp,
    D.diag_right, D.diag_left, M.tensor_comp, M.rightIn_Out, M.leftIn_Out, M.tensor_id]

def pair {X A B : Obj} (f : C.Hom X A) (g : C.Hom X B) : C.Hom X (M.obj A B) :=
  C.comp (D.diag X) (M.tensor f g)

theorem pair_fst {X A B : Obj} (f : C.Hom X A) (g : C.Hom X B) :
    C.comp (D.pair f g) (D.fst A B) = f := by
  rw [pair, C.assoc, ← D.fst_nat, ← C.assoc, D.diag_fst, C.id_comp]

theorem pair_snd {X A B : Obj} (f : C.Hom X A) (g : C.Hom X B) :
    C.comp (D.pair f g) (D.snd A B) = g := by
  rw [pair, C.assoc, ← D.snd_nat, ← C.assoc, D.diag_snd, C.id_comp]

theorem pair_eta {X A B : Obj} (f : C.Hom X (M.obj A B)) :
    D.pair (C.comp f (D.fst A B)) (C.comp f (D.snd A B)) = f := by
  rw [pair, ← M.tensor_comp, ← C.assoc, D.diag_nat, C.assoc, D.diag_projections, C.comp_id]

end DiagonalData

end DosenPetric
