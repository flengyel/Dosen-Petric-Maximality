module

public import DosenPetric.ReducedLaws
public import DosenPetric.ReducedOccurrences

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u

/-- A selected position, rather than a formula to be replaced wherever it occurs. -/
inductive Context (P : Type u) where
  | hole
  | left (o : Op) (C : NormalForm P) (K : Context P)
  | right (o : Op) (K : Context P) (C : NormalForm P)

namespace Context
variable {P : Type u}

@[reducible] def plug : Context P → NormalForm P → NormalForm P
  | .hole, A => A
  | .left o C K, A => o.formula C (K.plug A)
  | .right o K C, A => o.formula (K.plug A) C

def mapTerm {A B : NormalForm P} : (K : Context P) → Term P A B → Term P (K.plug A) (K.plug B)
  | .hole, f => f
  | .left o C K, f => .tensor o (.id C) (K.mapTerm f)
  | .right o K C, f => .tensor o (K.mapTerm f) (.id C)

theorem map_derives {A B : NormalForm P} (K : Context P) {f g : Term P A B}
    (h : Derives f g) : Derives (K.mapTerm f) (K.mapTerm g) := by
  induction K with
  | hole => exact h
  | left o C K ih => exact .tensor o (.refl _) ih
  | right o K C ih => exact .tensor o ih (.refl _)

/-- Defined only after preservation of the generating congruence. -/
def map {A B : NormalForm P} (K : Context P) (f : Hom A B) : Hom (K.plug A) (K.plug B) :=
  Quotient.liftOn f (fun t => ofTerm (K.mapTerm t)) (fun _ _ h => sound (K.map_derives h))

theorem map_ofTerm {A B : NormalForm P} (K : Context P) (f : Term P A B) :
    K.map (ofTerm f) = ofTerm (K.mapTerm f) := rfl

theorem map_left {A B : NormalForm P} (o : Op) (C : NormalForm P) (K : Context P) (f : Hom A B) :
    (left o C K).map f = tensor o (id C) (K.map f) := by
  induction f using Quotient.inductionOn with | h f => rfl

theorem map_right {A B : NormalForm P} (o : Op) (C : NormalForm P) (K : Context P) (f : Hom A B) :
    (right o K C).map f = tensor o (K.map f) (id C) := by
  induction f using Quotient.inductionOn with | h f => rfl

theorem map_hole {A B : NormalForm P} (f : Hom A B) : hole.map f = f := by
  induction f using Quotient.inductionOn with | h f => rfl

theorem map_id (K : Context P) (A : NormalForm P) : K.map (id A) = id (K.plug A) := by
  induction K with
  | hole => rfl
  | left o C K ih => rw [map_left, ih, Laws.tensor_id]
  | right o K C ih => rw [map_right, ih, Laws.tensor_id]

theorem map_comp {A B C : NormalForm P} (K : Context P) (f : Hom A B) (g : Hom B C) :
    K.map (comp f g) = comp (K.map f) (K.map g) := by
  induction K with
  | hole => simp only [map_hole]
  | left o D K ih => rw [map_left, map_left, map_left, Laws.tensor_comp, Laws.id_comp, ih]
  | right o K D ih => rw [map_right, map_right, map_right, Laws.tensor_comp, Laws.id_comp, ih]

theorem mapTerm_id (K : Context P) (A : NormalForm P) :
    Derives (K.mapTerm (.id A)) (.id (K.plug A)) := Quotient.exact (K.map_id A)

theorem mapTerm_comp {A B C : NormalForm P} (K : Context P) (f : Term P A B) (g : Term P B C) :
    Derives (K.mapTerm (.comp f g)) (.comp (K.mapTerm f) (K.mapTerm g)) :=
  Quotient.exact (K.map_comp (ofTerm f) (ofTerm g))

end Context
end DosenPetric.Reduced
