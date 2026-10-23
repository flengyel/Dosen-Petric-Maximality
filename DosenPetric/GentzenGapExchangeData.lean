module

public import DosenPetric.GentzenGapExchangeIndices

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.GapExchange
universe u
variable {P : Type u}

/-- Coordinates and numerical facts, all supplied by the two concrete constructors. -/
structure Data (P : Type u) where
  C : NormalForm P
  X : List (NormalForm P)
  Y : List (NormalForm P)
  gs0 : List (List (NormalForm P))
  gs1 : List (List (NormalForm P))
  tail0 : List (NormalForm P)
  tail1 : List (NormalForm P)
  upBefore : List (NormalForm P)
  upAfter : List (NormalForm P)
  loBefore : List (NormalForm P)
  loAfter : List (NormalForm P)
  upper0 : repeated C gs0 ++ tail0 = upBefore ++ X ++ Y ++ upAfter
  upper1 : repeated C gs1 ++ tail1 = upBefore ++ Y ++ X ++ upAfter
  lower0 : gaps gs0 ++ C :: tail0 = loBefore ++ X ++ Y ++ loAfter
  lower1 : gaps gs1 ++ C :: tail1 = loBefore ++ Y ++ X ++ loAfter
  count_eq : gs1.length = gs0.length
  squareIndex : ∀ i, copyIndex gs1 (exchangeIndex upBefore.length X.length Y.length i) =
    exchangeIndex loBefore.length X.length Y.length (copyIndex gs0 i)
  outside0 : ∀ i, i ∈ copyOffsets gs0 → i < upBefore.length ∨ upBefore.length+X.length+Y.length ≤ i
  retainedIndex : exchangeIndex loBefore.length X.length Y.length (gaps gs0).length = (gaps gs1).length

def interior (C : NormalForm P) (pre post : List (List (NormalForm P)))
    (U X Y V Θ : List (NormalForm P)) : Data P where
  C := C; X := X; Y := Y
  gs0 := pre ++ (U ++ X ++ Y ++ V) :: post
  gs1 := pre ++ (U ++ Y ++ X ++ V) :: post
  tail0 := Θ; tail1 := Θ
  upBefore := repeated C pre ++ U
  upAfter := V ++ C :: (repeated C post ++ Θ)
  loBefore := gaps pre ++ U
  loAfter := V ++ (gaps post ++ C :: Θ)
  upper0 := by simp only [GapInsertion.repeated_append,repeated,List.append_assoc,List.cons_append]
  upper1 := by simp only [GapInsertion.repeated_append,repeated,List.append_assoc,List.cons_append]
  lower0 := by simp only [GapInsertion.gaps_append,gaps,List.append_assoc]
  lower1 := by simp only [GapInsertion.gaps_append,gaps,List.append_assoc]
  count_eq := by simp only [List.length_append,List.length_cons]
  squareIndex := copyIndex_interior C pre post U X Y V
  outside0 := selected_interior_outside C pre post U X Y V
  retainedIndex := (exchange_outside _ _ _ _ (.inr (lower_end_le pre post U X Y V))).trans
    (gaps_length pre post U X Y V).symm

def terminal (C : NormalForm P) (gs : List (List (NormalForm P)))
    (U X Y V : List (NormalForm P)) : Data P where
  C := C; X := X; Y := Y
  gs0 := gs; gs1 := gs
  tail0 := U ++ X ++ Y ++ V
  tail1 := U ++ Y ++ X ++ V
  upBefore := repeated C gs ++ U; upAfter := V
  loBefore := gaps gs ++ C :: U; loAfter := V
  upper0 := by simp only [List.append_assoc]
  upper1 := by simp only [List.append_assoc]
  lower0 := by simp only [List.append_assoc,List.cons_append]
  lower1 := by simp only [List.append_assoc,List.cons_append]
  count_eq := rfl
  squareIndex := by
    intro i
    have he : (gaps gs).length+1+U.length = (gaps gs).length+(U.length+1) := by omega
    simpa only [List.length_append,List.length_cons,he] using copyIndex_tail C gs U.length X.length Y.length i
  outside0 := by
    intro i hi
    have h := selected_lt_repeated C gs i hi
    exact .inl (by simp only [List.length_append]; omega)
  retainedIndex := exchange_outside _ _ _ _ (.inl (by simp only [List.length_append,List.length_cons]; omega))

namespace Data
variable (d : Data P)

abbrev U0 := d.upBefore ++ d.X ++ d.Y ++ d.upAfter
abbrev U1 := d.upBefore ++ d.Y ++ d.X ++ d.upAfter
abbrev K0 := d.loBefore ++ d.X ++ d.Y ++ d.loAfter
abbrev K1 := d.loBefore ++ d.Y ++ d.X ++ d.loAfter

def c0 : Route d.K0 d.U0 := (copies d.C d.gs0 d.tail0).cast d.lower0 d.upper0
def c1 : Route d.K1 d.U1 := (copies d.C d.gs1 d.tail1).cast d.lower1 d.upper1

def swapUpper {A : NormalForm P} (a : At d.U0 A) : At d.U1 A :=
  a.swapBlocks d.upBefore d.X d.Y d.upAfter

def swapLower {A : NormalForm P} (a : At d.K0 A) : At d.K1 A :=
  a.swapBlocks d.loBefore d.X d.Y d.loAfter

def keep0 : At d.K0 d.C := (At.shift (gaps d.gs0) (.here d.C d.tail0)).cast d.lower0
def keep1 : At d.K1 d.C := (At.shift (gaps d.gs1) (.here d.C d.tail1)).cast d.lower1

def selected0 := (selectedCopies d.C d.gs0 d.tail0).map (At.cast d.upper0)
def selected1 := (selectedCopies d.C d.gs1 d.tail1).map (At.cast d.upper1)

theorem c0_index {A : NormalForm P} (a : At d.U0 A) :
    (d.c0.get a).index = copyIndex d.gs0 a.index := by
  simp only [c0,Route.get_index_cast,copies_index,At.index_cast]

theorem c1_index {A : NormalForm P} (a : At d.U1 A) :
    (d.c1.get a).index = copyIndex d.gs1 a.index := by
  simp only [c1,Route.get_index_cast,copies_index,At.index_cast]

theorem swapUpper_index {A : NormalForm P} (a : At d.U0 A) :
    (d.swapUpper a).index = exchangeIndex d.upBefore.length d.X.length d.Y.length a.index := swapBlocks_index ..

theorem swapLower_index {A : NormalForm P} (a : At d.K0 A) :
    (d.swapLower a).index = exchangeIndex d.loBefore.length d.X.length d.Y.length a.index := swapBlocks_index ..

theorem keep0_index : d.keep0.index = (gaps d.gs0).length := by
  simp only [keep0,At.index_cast,At.index_shift,At.index,Nat.add_zero]

theorem keep1_index : d.keep1.index = (gaps d.gs1).length := by
  simp only [keep1,At.index_cast,At.index_shift,At.index,Nat.add_zero]

theorem square {A : NormalForm P} (a : At d.U0 A) :
    d.c1.get (d.swapUpper a) = d.swapLower (d.c0.get a) := by
  apply At.index_injective
  rw [c1_index,swapUpper_index,swapLower_index,c0_index]
  exact d.squareIndex a.index

theorem retained : d.swapLower d.keep0 = d.keep1 := by
  apply At.index_injective
  rw [swapLower_index,keep0_index,keep1_index]
  exact d.retainedIndex

end Data
end DosenPetric.Reduced.Gentzen.GapExchange
