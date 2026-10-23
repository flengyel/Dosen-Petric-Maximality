module

public import DosenPetric.GentzenGapExchangeRouting

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.GapLogical
universe u
variable {P : Type u}

/-- Numerical shadow of a partial fixed-block map; never a typed map A/B to D. -/
def parentIndex (k n m i : Nat) : Option Nat :=
  if i < k then some i else if i < k+n then none else some (i-n+m)

theorem parent_add (a k n m i : Nat) : parentIndex (a+k) n m (a+i) =
    (parentIndex k n m i).map (fun j => a+j) := by
  unfold parentIndex
  repeat first | split | simp only [Option.map_some,Option.map_none,Option.some.injEq] | omega

theorem parent_before (k n m i : Nat) (h : i < k) : parentIndex k n m i = some i := by
  simp only [parentIndex,ite_eq_left h]

theorem copy_after (Γ : List (NormalForm P)) (gs : List (List (NormalForm P))) (i : Nat) :
    copyIndex (Γ :: gs) (Γ.length+1+i) = Γ.length + copyIndex gs i := by
  rw [copyIndex,ite_eq_right (by omega),ite_eq_right (by omega)]
  congr 2
  omega

theorem gaps_length (pre post : List (List (NormalForm P))) (U V : List (NormalForm P))
    (A B D : NormalForm P) :
    (gaps (pre ++ (U ++ A :: B :: V) :: post)).length =
      (gaps (pre ++ (U ++ D :: V) :: post)).length + 1 := by
  simp only [GapInsertion.gaps_append,gaps,List.length_append,List.length_cons]
  omega

theorem lower_end_le (pre post : List (List (NormalForm P))) (U V : List (NormalForm P))
    (A B : NormalForm P) :
    (gaps pre ++ U).length+2 ≤ (gaps (pre ++ (U ++ A :: B :: V) :: post)).length := by
  simp only [GapInsertion.gaps_append,gaps,List.length_append,List.length_cons]
  omega

theorem copyIndex_interior (C A B D : NormalForm P) (pre post : List (List (NormalForm P)))
    (U V : List (NormalForm P)) (i : Nat) :
    (parentIndex (repeated C pre ++ U).length 2 1 i).map
      (copyIndex (pre ++ (U ++ D :: V) :: post)) =
    parentIndex (gaps pre ++ U).length 2 1 (copyIndex (pre ++ (U ++ A :: B :: V) :: post) i) := by
  induction pre generalizing i with
  | nil =>
    simp only [List.nil_append,repeated,List.nil_append]
    by_cases hi : i < U.length
    · rw [parent_before _ _ _ _ hi,Option.map_some,copyIndex,
        ite_eq_left (by simp only [List.length_append,List.length_cons]; omega),copyIndex,
        ite_eq_left (by simp only [List.length_append,List.length_cons]; omega),parent_before _ _ _ _ hi]
    · by_cases hm : i < U.length+2
      · have hci : copyIndex ((U ++ A :: B :: V) :: post) i = i := by
          rw [copyIndex,ite_eq_left (by simp only [List.length_append,List.length_cons]; omega)]
        rw [hci]
        simp only [parentIndex,ite_eq_right hi,ite_eq_left hm,Option.map_none]
      · rw [parentIndex,ite_eq_right hi,ite_eq_right hm,Option.map_some]
        simp only [copyIndex,List.length_append,List.length_cons]
        by_cases hv : i < U.length+(V.length+1+1)
        · rw [ite_eq_left hv,ite_eq_left (by omega)]
          simp only [parentIndex]
          rw [ite_eq_right hi,ite_eq_right hm]
        · by_cases he : i = U.length+(V.length+1+1)
          · rw [ite_eq_right hv,ite_eq_left he,ite_eq_right (by omega),ite_eq_left (by omega)]
            unfold parentIndex
            repeat first | split | simp only [Option.some.injEq] | omega
          · rw [ite_eq_right hv,ite_eq_right he,ite_eq_right (by omega),ite_eq_right (by omega)]
            have hh : i-2+1-(U.length+(V.length+1))-1 = i-(U.length+(V.length+1+1))-1 := by omega
            rw [hh]
            unfold parentIndex
            repeat first | split | simp only [Option.some.injEq] | omega
  | cons Γ pre ih =>
    have hl := gaps_length pre post U V A B D
    have hk := lower_end_le pre post U V A B
    simp only [List.cons_append,repeated,gaps,List.length_append,List.length_cons] at *
    by_cases hi : i < Γ.length
    · rw [parent_before _ _ _ _ (by omega),Option.map_some,copyIndex,ite_eq_left hi,
        copyIndex,ite_eq_left hi,parent_before _ _ _ _ (by omega)]
    · by_cases he : i = Γ.length
      · subst i
        rw [parent_before _ _ _ _ (by omega),Option.map_some,copyIndex,
          ite_eq_right (Nat.lt_irrefl _),ite_eq_left rfl,
          copyIndex,ite_eq_right (Nat.lt_irrefl _),ite_eq_left rfl]
        unfold parentIndex
        repeat first | split | simp only [Option.some.injEq] | omega
      · have heq : i = Γ.length+1+(i-Γ.length-1) := by omega
        have hc : Γ.length+((repeated C pre).length+1)+U.length =
            (Γ.length+1)+((repeated C pre).length+U.length) := by omega
        have hc' : Γ.length+(gaps pre).length+U.length = Γ.length+((gaps pre).length+U.length) := by omega
        rw [hc,heq,parent_add,copy_after,hc',parent_add]
        have hh := ih (i-Γ.length-1)
        cases hp : parentIndex ((repeated C pre).length+U.length) 2 1 (i-Γ.length-1) with
        | none =>
          simp only [hp,Option.map_none] at hh ⊢
          rw [← hh]
          rfl
        | some j =>
          simp only [hp,Option.map_some] at hh ⊢
          rw [copy_after,← hh]
          rfl

theorem copyIndex_tail (C : NormalForm P) (gs : List (List (NormalForm P))) (u i : Nat) :
    (parentIndex ((repeated C gs).length+u) 2 1 i).map (copyIndex gs) =
    parentIndex ((gaps gs).length+1+u) 2 1 (copyIndex gs i) := by
  induction gs generalizing i with
  | nil =>
    simp only [repeated,gaps,List.length_nil,Nat.zero_add,copyIndex]
    unfold parentIndex
    repeat first | split | simp only [Option.map_some,Option.map_none,Option.some.injEq] | omega
  | cons Γ gs ih =>
    simp only [repeated,gaps,List.length_append,List.length_cons]
    by_cases hi : i < Γ.length
    · rw [parent_before _ _ _ _ (by omega),Option.map_some,copyIndex,ite_eq_left hi,
        parent_before _ _ _ _ (by omega)]
    · by_cases he : i = Γ.length
      · subst i
        rw [parent_before _ _ _ _ (by omega),Option.map_some,copyIndex,
          ite_eq_right (Nat.lt_irrefl _),ite_eq_left rfl,parent_before _ _ _ _ (by omega)]
      · have heq : i = Γ.length+1+(i-Γ.length-1) := by omega
        have hc : Γ.length+((repeated C gs).length+1)+u = (Γ.length+1)+((repeated C gs).length+u) := by omega
        have hc' : Γ.length+(gaps gs).length+1+u = Γ.length+((gaps gs).length+1+u) := by omega
        rw [hc,heq,parent_add,copy_after,hc',parent_add]
        have hh := ih (i-Γ.length-1)
        cases hp : parentIndex ((repeated C gs).length+u) 2 1 (i-Γ.length-1) with
        | none => simp only [hp,Option.map_none] at hh ⊢; rw [← hh]; rfl
        | some j => simp only [hp,Option.map_some] at hh ⊢; rw [copy_after,← hh]; rfl

theorem selected_outside (C : NormalForm P) (pre post : List (List (NormalForm P)))
    (U X V : List (NormalForm P)) (i : Nat)
    (h : i ∈ copyOffsets (pre ++ (U ++ (X ++ V)) :: post)) :
    i < (repeated C pre ++ U).length ∨ (repeated C pre ++ U).length+X.length ≤ i := by
  have h' : i ∈ copyOffsets (pre ++ (U ++ X ++ [] ++ V) :: post) := by
    simpa only [List.append_nil,List.append_assoc] using h
  have hh := GapExchange.selected_interior_outside C pre post U X [] V i h'
  simpa only [List.length_nil,Nat.add_zero] using hh

end DosenPetric.Reduced.Gentzen.GapLogical
