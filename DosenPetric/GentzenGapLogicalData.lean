module

public import DosenPetric.GentzenLogicalPositions

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.GapLogical
universe u
variable {P : Type u}

structure Data (P : Type u) (o : Op) where
  A : NormalForm P
  B : NormalForm P
  C : NormalForm P
  gs0 : List (List (NormalForm P))
  gs1 : List (List (NormalForm P))
  tail0 : List (NormalForm P)
  tail1 : List (NormalForm P)
  upBefore : List (NormalForm P)
  upAfter : List (NormalForm P)
  loBefore : List (NormalForm P)
  loAfter : List (NormalForm P)
  upper0 : repeated C gs0 ++ tail0 = upBefore ++ A :: B :: upAfter
  upper1 : repeated C gs1 ++ tail1 = upBefore ++ o.formula A B :: upAfter
  lower0 : gaps gs0 ++ C :: tail0 = loBefore ++ A :: B :: loAfter
  lower1 : gaps gs1 ++ C :: tail1 = loBefore ++ o.formula A B :: loAfter
  count_eq : gs1.length = gs0.length
  squareIndex : ∀ i, (parentIndex upBefore.length 2 1 i).map (copyIndex gs1) =
    parentIndex loBefore.length 2 1 (copyIndex gs0 i)
  outside0 : ∀ i, i ∈ copyOffsets gs0 → i < upBefore.length ∨ upBefore.length+2 ≤ i
  outside1 : ∀ i, i ∈ copyOffsets gs1 → i < upBefore.length ∨ upBefore.length+1 ≤ i
  retainedIndex : parentIndex loBefore.length 2 1 (gaps gs0).length = some (gaps gs1).length
  principalIndex : copyIndex gs1 upBefore.length = loBefore.length
  firstIndex : copyIndex gs0 upBefore.length = loBefore.length
  secondIndex : copyIndex gs0 (upBefore.length+1) = loBefore.length+1
  principalDistinct : loBefore.length ≠ (gaps gs1).length

def interior (o : Op) (A B C : NormalForm P) (pre post : List (List (NormalForm P)))
    (U V Θ : List (NormalForm P)) : Data P o where
  A := A; B := B; C := C
  gs0 := pre ++ (U ++ A :: B :: V) :: post
  gs1 := pre ++ (U ++ o.formula A B :: V) :: post
  tail0 := Θ; tail1 := Θ
  upBefore := repeated C pre ++ U
  upAfter := V ++ C :: (repeated C post ++ Θ)
  loBefore := gaps pre ++ U
  loAfter := V ++ (gaps post ++ C :: Θ)
  upper0 := by simp only [GapInsertion.repeated_append,repeated,List.append_assoc,List.cons_append]
  upper1 := by simp only [GapInsertion.repeated_append,repeated,List.append_assoc,List.cons_append]
  lower0 := by simp only [GapInsertion.gaps_append,gaps,List.append_assoc,List.cons_append]
  lower1 := by simp only [GapInsertion.gaps_append,gaps,List.append_assoc,List.cons_append]
  count_eq := by simp only [List.length_append,List.length_cons]
  squareIndex := copyIndex_interior C A B (o.formula A B) pre post U V
  outside0 := by
    intro i hi
    exact selected_outside C pre post U [A,B] V i hi
  outside1 := by
    intro i hi
    exact selected_outside C pre post U [o.formula A B] V i hi
  retainedIndex := by
    have hl := gaps_length pre post U V A B (o.formula A B)
    have hk := lower_end_le pre post U V A B
    unfold parentIndex
    repeat first | split | simp only [Option.some.injEq] | omega
  principalIndex := GapInsertion.copyIndex_interior_inserted C (o.formula A B) pre post U V
  firstIndex := GapInsertion.copyIndex_interior_inserted C A pre post U (B :: V)
  secondIndex := by
    have h := GapInsertion.copyIndex_interior_inserted C B pre post (U ++ [A]) V
    simpa only [List.append_assoc,List.singleton_append,List.length_append,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_assoc] using h
  principalDistinct := by
    have h := GapInsertion.interior_cut_le pre post U V
    have hl := GapInsertion.interior_gaps_length pre post U V (o.formula A B)
    omega

def terminal (o : Op) (A B C : NormalForm P) (gs : List (List (NormalForm P)))
    (U V : List (NormalForm P)) : Data P o where
  A := A; B := B; C := C
  gs0 := gs; gs1 := gs
  tail0 := U ++ A :: B :: V; tail1 := U ++ o.formula A B :: V
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
  outside0 := by
    intro i hi
    have h := GapExchange.selected_lt_repeated C gs i hi
    exact .inl (by simp only [List.length_append]; omega)
  outside1 := by
    intro i hi
    have h := GapExchange.selected_lt_repeated C gs i hi
    exact .inl (by simp only [List.length_append]; omega)
  retainedIndex := parent_before _ _ _ _ (by simp only [List.length_append,List.length_cons]; omega)
  principalIndex := by
    have h := GapInsertion.copyIndex_tail_inserted C gs U.length
    simpa only [List.length_append,List.length_cons,Nat.add_assoc,Nat.add_comm] using h
  firstIndex := by
    have h := GapInsertion.copyIndex_tail_inserted C gs U.length
    simpa only [List.length_append,List.length_cons,Nat.add_assoc,Nat.add_comm] using h
  secondIndex := by
    simp only [List.length_append,List.length_cons]
    have hc : (repeated C gs).length+U.length+1 = (repeated C gs).length+(U.length+1) := by omega
    rw [hc,GapInsertion.copyIndex_tail_inserted C gs (U.length+1)]
    omega
  principalDistinct := by simp only [List.length_append,List.length_cons]; omega

namespace Data
variable {o : Op} (d : Data P o)

abbrev D := o.formula d.A d.B
abbrev U0 := d.upBefore ++ d.A :: d.B :: d.upAfter
abbrev U1 := d.upBefore ++ d.D :: d.upAfter
abbrev K0 := d.loBefore ++ d.A :: d.B :: d.loAfter
abbrev K1 := d.loBefore ++ d.D :: d.loAfter

def c0 : Route d.K0 d.U0 := (copies d.C d.gs0 d.tail0).cast d.lower0 d.upper0
def c1 : Route d.K1 d.U1 := (copies d.C d.gs1 d.tail1).cast d.lower1 d.upper1

def uParent {E : NormalForm P} : At d.U0 E → Option (At d.U1 E) := At.fixed d.upBefore [d.A,d.B] [d.D] d.upAfter
def kParent {E : NormalForm P} : At d.K0 E → Option (At d.K1 E) := At.fixed d.loBefore [d.A,d.B] [d.D] d.loAfter

def keep0 : At d.K0 d.C := (At.shift (gaps d.gs0) (.here d.C d.tail0)).cast d.lower0
def keep1 : At d.K1 d.C := (At.shift (gaps d.gs1) (.here d.C d.tail1)).cast d.lower1

def zUpper : At d.U1 d.D := At.shift d.upBefore (.here d.D d.upAfter)
def zLower : At d.K1 d.D := At.shift d.loBefore (.here d.D d.loAfter)
def aUpper : At d.U0 d.A := At.shift d.upBefore (.here d.A (d.B :: d.upAfter))
def bUpper : At d.U0 d.B := At.shift d.upBefore (.there (.here d.B d.upAfter))
def aLower : At d.K0 d.A := At.shift d.loBefore (.here d.A (d.B :: d.loAfter))
def bLower : At d.K0 d.B := At.shift d.loBefore (.there (.here d.B d.loAfter))
def selected0 := (selectedCopies d.C d.gs0 d.tail0).map (At.cast d.upper0)
def selected1 := (selectedCopies d.C d.gs1 d.tail1).map (At.cast d.upper1)

theorem c0_index {E : NormalForm P} (a : At d.U0 E) : (d.c0.get a).index = copyIndex d.gs0 a.index := by
  simp only [c0,Route.get_index_cast,copies_index,At.index_cast]
theorem c1_index {E : NormalForm P} (a : At d.U1 E) : (d.c1.get a).index = copyIndex d.gs1 a.index := by
  simp only [c1,Route.get_index_cast,copies_index,At.index_cast]
theorem keep0_index : d.keep0.index = (gaps d.gs0).length := by
  simp only [keep0,At.index_cast,At.index_shift,At.index,Nat.add_zero]
theorem keep1_index : d.keep1.index = (gaps d.gs1).length := by
  simp only [keep1,At.index_cast,At.index_shift,At.index,Nat.add_zero]

theorem square {E : NormalForm P} (a : At d.U0 E) :
    (d.uParent a).map d.c1.get = d.kParent (d.c0.get a) := by
  apply At.option_index_injective
  have h0 := At.fixed_index d.upBefore [d.A,d.B] [d.D] d.upAfter a
  have h1 := At.fixed_index d.loBefore [d.A,d.B] [d.D] d.loAfter (d.c0.get a)
  change (d.uParent a).map At.index = parentIndex d.upBefore.length 2 1 a.index at h0
  change (d.kParent (d.c0.get a)).map At.index = parentIndex d.loBefore.length 2 1 (d.c0.get a).index at h1
  rw [d.c0_index] at h1
  rw [Option.map_map]
  have he : ((d.uParent a).map (fun b => (d.c1.get b).index)) =
      ((d.uParent a).map At.index).map (copyIndex d.gs1) := by
    cases d.uParent a with
    | none => rfl
    | some b => exact congrArg some (d.c1_index b)
  exact he.trans ((congrArg (Option.map (copyIndex d.gs1)) h0).trans ((d.squareIndex a.index).trans h1.symm))

theorem principal : d.c1.get d.zUpper = d.zLower := by
  apply At.index_injective
  simp only [c1_index,zUpper,zLower,At.index_shift,At.index,Nat.add_zero]
  exact d.principalIndex

theorem first : d.c0.get d.aUpper = d.aLower := by
  apply At.index_injective
  simp only [c0_index,aUpper,aLower,At.index_shift,At.index,Nat.add_zero]
  exact d.firstIndex

theorem second : d.c0.get d.bUpper = d.bLower := by
  apply At.index_injective
  simp only [c0_index,bUpper,bLower,At.index_shift,At.index]
  exact d.secondIndex

end Data
end DosenPetric.Reduced.Gentzen.GapLogical
