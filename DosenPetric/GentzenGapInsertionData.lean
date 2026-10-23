module

public import DosenPetric.GentzenGapInsertionIndices

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.GapInsertion
universe u
variable {P : Type u}

/-- Concrete context coordinates and their numerical routing laws.
    Both constructors below prove these fields from the published copies routes. -/
structure Data (P : Type u) where
  C : NormalForm P
  E : NormalForm P
  gs0 : List (List (NormalForm P))
  gs1 : List (List (NormalForm P))
  tail0 : List (NormalForm P)
  tail1 : List (NormalForm P)
  upBefore : List (NormalForm P)
  upAfter : List (NormalForm P)
  loBefore : List (NormalForm P)
  loAfter : List (NormalForm P)
  upper0 : repeated C gs0 ++ tail0 = upBefore ++ upAfter
  upper1 : repeated C gs1 ++ tail1 = upBefore ++ E :: upAfter
  lower0 : gaps gs0 ++ C :: tail0 = loBefore ++ loAfter
  lower1 : gaps gs1 ++ C :: tail1 = loBefore ++ E :: loAfter
  count_eq : gs1.length = gs0.length
  squareIndex : ∀ i, copyIndex gs1 (liftIndex upBefore.length i) =
    liftIndex loBefore.length (copyIndex gs0 i)
  insertedIndex : copyIndex gs1 upBefore.length = loBefore.length
  retainedIndex : liftIndex loBefore.length (gaps gs0).length = (gaps gs1).length
  lowerOrder : loBefore.length < (gaps gs1).length ∨ (gaps gs1).length < loBefore.length

def interior (C E : NormalForm P) (pre post : List (List (NormalForm P)))
    (U V Θ : List (NormalForm P)) : Data P where
  C := C; E := E
  gs0 := pre ++ (U ++ V) :: post
  gs1 := pre ++ (U ++ E :: V) :: post
  tail0 := Θ; tail1 := Θ
  upBefore := repeated C pre ++ U
  upAfter := V ++ C :: (repeated C post ++ Θ)
  loBefore := gaps pre ++ U
  loAfter := V ++ (gaps post ++ C :: Θ)
  upper0 := by simp only [repeated_append,repeated,List.append_assoc,List.cons_append]
  upper1 := by simp only [repeated_append,repeated,List.append_assoc,List.cons_append]
  lower0 := by simp only [gaps_append,gaps,List.append_assoc]
  lower1 := by simp only [gaps_append,gaps,List.append_assoc,List.cons_append]
  count_eq := by simp only [List.length_append,List.length_cons]
  squareIndex := copyIndex_interior C E pre post U V
  insertedIndex := copyIndex_interior_inserted C E pre post U V
  retainedIndex := by
    have h := interior_gaps_length pre post U V E
    have hk := interior_cut_le pre post U V
    unfold liftIndex
    split <;> omega
  lowerOrder := by
    have h := interior_gaps_length pre post U V E
    have hk := interior_cut_le pre post U V
    exact .inl (by omega)

def terminal (C E : NormalForm P) (gs : List (List (NormalForm P)))
    (U V : List (NormalForm P)) : Data P where
  C := C; E := E
  gs0 := gs; gs1 := gs
  tail0 := U ++ V; tail1 := U ++ E :: V
  upBefore := repeated C gs ++ U; upAfter := V
  loBefore := gaps gs ++ C :: U; loAfter := V
  upper0 := (List.append_assoc ..).symm
  upper1 := (List.append_assoc ..).symm
  lower0 := by simp only [List.append_assoc,List.cons_append]
  lower1 := by simp only [List.append_assoc,List.cons_append]
  count_eq := rfl
  squareIndex := by
    intro i
    have he : (gaps gs).length+1+U.length = (gaps gs).length+(U.length+1) := by omega
    simpa only [List.length_append,List.length_cons,he] using copyIndex_tail C gs U.length i
  insertedIndex := by
    have he : (gaps gs).length+1+U.length = (gaps gs).length+(U.length+1) := by omega
    simpa only [List.length_append,List.length_cons,he] using copyIndex_tail_inserted C gs U.length
  retainedIndex := by
    unfold liftIndex
    have h : (gaps gs).length < (gaps gs ++ C :: U).length := by
      simp only [List.length_append,List.length_cons]
      omega
    rw [ite_eq_left h]
  lowerOrder := .inr (by simp only [List.length_append,List.length_cons]; omega)

theorem index_formula_cast {Γ : List (NormalForm P)} {A B : NormalForm P}
    (h : A = B) (a : At Γ A) : (h ▸ a).index = a.index := by cases h; rfl

namespace Data
variable (d : Data P)

abbrev U0 := d.upBefore ++ d.upAfter
abbrev U1 := d.upBefore ++ d.E :: d.upAfter
abbrev K0 := d.loBefore ++ d.loAfter
abbrev K1 := d.loBefore ++ d.E :: d.loAfter

def c0 : Route d.K0 d.U0 := (copies d.C d.gs0 d.tail0).cast d.lower0 d.upper0
def c1 : Route d.K1 d.U1 := (copies d.C d.gs1 d.tail1).cast d.lower1 d.upper1
def tUpper : Route d.U1 d.U0 := Route.thin d.upBefore d.upAfter d.E
def tLower : Route d.K1 d.K0 := Route.thin d.loBefore d.loAfter d.E
def keep0 : At d.K0 d.C := (At.shift (gaps d.gs0) (.here d.C d.tail0)).cast d.lower0
def keep1 : At d.K1 d.C := (At.shift (gaps d.gs1) (.here d.C d.tail1)).cast d.lower1
def zUpper : At d.U1 d.E := At.shift d.upBefore (.here d.E d.upAfter)
def zLower : At d.K1 d.E := At.shift d.loBefore (.here d.E d.loAfter)
def selected0 : List (At d.U0 d.C) := (selectedCopies d.C d.gs0 d.tail0).map (At.cast d.upper0)
def selected1 : List (At d.U1 d.C) := (selectedCopies d.C d.gs1 d.tail1).map (At.cast d.upper1)

theorem c0_index {A : NormalForm P} (a : At d.U0 A) :
    (d.c0.get a).index = copyIndex d.gs0 a.index := by
  simp only [c0,Route.get_index_cast,copies_index,At.index_cast]

theorem c1_index {A : NormalForm P} (a : At d.U1 A) :
    (d.c1.get a).index = copyIndex d.gs1 a.index := by
  simp only [c1,Route.get_index_cast,copies_index,At.index_cast]

theorem tUpper_index {A : NormalForm P} (a : At d.U0 A) :
    (d.tUpper.get a).index = liftIndex d.upBefore.length a.index := thin_index ..

theorem tLower_index {A : NormalForm P} (a : At d.K0 A) :
    (d.tLower.get a).index = liftIndex d.loBefore.length a.index := thin_index ..

theorem keep0_index : d.keep0.index = (gaps d.gs0).length := by
  simp only [keep0,At.index_cast,At.index_shift,At.index,Nat.add_zero]

theorem keep1_index : d.keep1.index = (gaps d.gs1).length := by
  simp only [keep1,At.index_cast,At.index_shift,At.index,Nat.add_zero]

theorem zUpper_index : d.zUpper.index = d.upBefore.length := by
  simp only [zUpper,At.index_shift,At.index,Nat.add_zero]

theorem zLower_index : d.zLower.index = d.loBefore.length := by
  simp only [zLower,At.index_shift,At.index,Nat.add_zero]

/-- The routing square applies to every old typed position. -/
theorem square {A : NormalForm P} (a : At d.U0 A) :
    d.c1.get (d.tUpper.get a) = d.tLower.get (d.c0.get a) := by
  apply At.index_injective
  rw [c1_index,tUpper_index,tLower_index,c0_index]
  exact d.squareIndex a.index

theorem retained : d.tLower.get d.keep0 = d.keep1 := by
  apply At.index_injective
  rw [tLower_index,keep0_index,keep1_index]
  exact d.retainedIndex

/-- This extra equation covers the new position omitted by the old-position square. -/
theorem inserted : d.c1.get d.zUpper = d.zLower := by
  apply At.index_injective
  rw [c1_index,zUpper_index,zLower_index]
  exact d.insertedIndex

theorem inserted_ne_retained : d.zLower.index ≠ d.keep1.index := by
  rw [zLower_index,keep1_index]
  cases d.lowerOrder <;> omega

theorem inserted_distinct {h : d.E = d.C} : d.zLower ≠ h.symm ▸ d.keep1 := by
  intro he
  apply d.inserted_ne_retained
  exact (congrArg At.index he).trans (index_formula_cast h.symm d.keep1)

theorem canonical_inserted : (copies d.C d.gs1 d.tail1).get (d.zUpper.cast d.upper1.symm) =
    d.zLower.cast d.lower1.symm := by
  apply At.index_injective
  rw [copies_index,At.index_cast,At.index_cast,zUpper_index,zLower_index]
  exact d.insertedIndex

theorem canonical_inserted_fixed : (d.zLower.cast d.lower1.symm).index ≠ (gaps d.gs1).length := by
  rw [At.index_cast,zLower_index]
  cases d.lowerOrder <;> omega

end Data
end DosenPetric.Reduced.Gentzen.GapInsertion
