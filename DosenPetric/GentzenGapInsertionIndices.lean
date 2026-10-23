module

public import DosenPetric.GentzenLogicalCommutationRank

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace GapInsertion

def liftIndex (k i : Nat) : Nat := if i < k then i else i + 1

theorem liftIndex_ne (k i : Nat) : liftIndex k i ≠ k := by
  unfold liftIndex
  split <;> omega

theorem liftIndex_injective (k i j : Nat) (h : liftIndex k i = liftIndex k j) : i = j := by
  unfold liftIndex at h
  split at h <;> split at h <;> omega

theorem liftIndex_add (a k i : Nat) : liftIndex (a+k) (a+i) = a + liftIndex k i := by
  unfold liftIndex
  split <;> split <;> omega

theorem gaps_append (pre post : List (List (NormalForm P))) :
    gaps (pre ++ post) = gaps pre ++ gaps post := by
  induction pre with
  | nil => rfl
  | cons Γ pre ih => simp only [List.cons_append,gaps,ih,List.append_assoc]

theorem repeated_append (C : NormalForm P) (pre post : List (List (NormalForm P))) :
    repeated C (pre ++ post) = repeated C pre ++ repeated C post := by
  induction pre with
  | nil => rfl
  | cons Γ pre ih => simp only [List.cons_append,repeated,ih,List.append_assoc,List.cons_append]

theorem interior_gaps_length (pre post : List (List (NormalForm P)))
    (U V : List (NormalForm P)) (E : NormalForm P) :
    (gaps (pre ++ (U ++ E :: V) :: post)).length =
      (gaps (pre ++ (U ++ V) :: post)).length + 1 := by
  simp only [gaps_append,gaps,List.length_append,List.length_cons]
  omega

theorem interior_cut_le (pre post : List (List (NormalForm P)))
    (U V : List (NormalForm P)) :
    (gaps pre ++ U).length ≤ (gaps (pre ++ (U ++ V) :: post)).length := by
  simp only [gaps_append,gaps,List.length_append]
  omega

/-- Insertion in a fixed gap commutes with the numerical copies map. -/
theorem copyIndex_interior (C E : NormalForm P) (pre post : List (List (NormalForm P)))
    (U V : List (NormalForm P)) (i : Nat) :
    copyIndex (pre ++ (U ++ E :: V) :: post)
        (liftIndex (repeated C pre ++ U).length i) =
      liftIndex (gaps pre ++ U).length (copyIndex (pre ++ (U ++ V) :: post) i) := by
  induction pre generalizing i with
  | nil =>
    simp only [List.nil_append,repeated,gaps]
    unfold liftIndex
    simp only [copyIndex,List.length_append,List.length_cons]
    repeat first | split | omega
    have he : i+1-(U.length+(V.length+1))-1 = i-(U.length+V.length)-1 := by omega
    rw [he]
    omega
  | cons Γ pre ih =>
    have hl := interior_gaps_length pre post U V E
    have hk := interior_cut_le pre post U V
    simp only [List.cons_append,repeated,gaps,List.length_append,List.length_cons] at *
    by_cases hi : i < Γ.length
    · have h₁ : i < Γ.length + (gaps pre).length + U.length := by omega
      have h₂ : i < Γ.length + ((repeated C pre).length + 1) + U.length := by omega
      simp only [liftIndex,copyIndex,ite_eq_left h₂,ite_eq_left hi,ite_eq_left h₁]
    · by_cases he : i = Γ.length
      · subst i
        have h₂ : Γ.length < Γ.length + ((repeated C pre).length + 1) + U.length := by omega
        rw [liftIndex,ite_eq_left h₂,copyIndex,ite_eq_right (Nat.lt_irrefl _),ite_eq_left rfl,
          copyIndex,ite_eq_right (Nat.lt_irrefl _),ite_eq_left rfl]
        unfold liftIndex
        split <;> omega
      · have hj : Γ.length + 1 ≤ i := by omega
        have hi' : i = (Γ.length+1) + (i-Γ.length-1) := by omega
        have hc : Γ.length + ((repeated C pre).length + 1) + U.length =
            (Γ.length+1) + ((repeated C pre).length+U.length) := by omega
        rw [hc,hi',liftIndex_add]
        have h₁ : ¬ Γ.length + 1 + liftIndex ((repeated C pre).length + U.length) (i-Γ.length-1) < Γ.length := by omega
        have h₂ : Γ.length + 1 + liftIndex ((repeated C pre).length + U.length) (i-Γ.length-1) ≠ Γ.length := by omega
        simp only [copyIndex,ite_eq_right h₁,ite_eq_right h₂]
        have ha : Γ.length + 1 + liftIndex ((repeated C pre).length+U.length) (i-Γ.length-1) - Γ.length - 1 =
            liftIndex ((repeated C pre).length+U.length) (i-Γ.length-1) := by omega
        rw [ha,ih]
        have hb : ¬ Γ.length + 1 + (i-Γ.length-1) < Γ.length := by omega
        have hd : Γ.length + 1 + (i-Γ.length-1) ≠ Γ.length := by omega
        rw [ite_eq_right hb,ite_eq_right hd]
        have heq : Γ.length + 1 + (i-Γ.length-1) - Γ.length - 1 = i-Γ.length-1 := by omega
        rw [heq]
        have hcut : Γ.length + (gaps pre).length + U.length = Γ.length + ((gaps pre).length+U.length) := by omega
        rw [hcut,liftIndex_add]

theorem copyIndex_tail (C : NormalForm P) (gs : List (List (NormalForm P)))
    (u i : Nat) : copyIndex gs (liftIndex ((repeated C gs).length+u) i) =
      liftIndex ((gaps gs).length+1+u) (copyIndex gs i) := by
  induction gs generalizing i with
  | nil =>
    simp only [repeated,gaps,List.length_nil,Nat.zero_add,copyIndex]
    unfold liftIndex
    repeat first | split | omega
  | cons Γ gs ih =>
    simp only [repeated,gaps,List.length_append,List.length_cons]
    by_cases hi : i < Γ.length
    · have h₁ : i < Γ.length + ((repeated C gs).length + 1) + u := by omega
      have h₂ : i < Γ.length + (gaps gs).length + 1 + u := by omega
      rw [liftIndex,ite_eq_left h₁,copyIndex,ite_eq_left hi,liftIndex,ite_eq_left h₂]
    · by_cases he : i = Γ.length
      · subst i
        have h₁ : Γ.length < Γ.length + ((repeated C gs).length + 1) + u := by omega
        rw [liftIndex,ite_eq_left h₁,copyIndex,ite_eq_right (Nat.lt_irrefl _),ite_eq_left rfl]
        unfold liftIndex
        split <;> omega
      · have hi' : i = (Γ.length+1) + (i-Γ.length-1) := by omega
        have hc : Γ.length+((repeated C gs).length+1)+u = (Γ.length+1)+((repeated C gs).length+u) := by omega
        rw [hc,hi',liftIndex_add]
        have h₁ : ¬ Γ.length+1+liftIndex ((repeated C gs).length+u) (i-Γ.length-1) < Γ.length := by omega
        have h₂ : Γ.length+1+liftIndex ((repeated C gs).length+u) (i-Γ.length-1) ≠ Γ.length := by omega
        simp only [copyIndex,ite_eq_right h₁,ite_eq_right h₂]
        have ha : Γ.length+1+liftIndex ((repeated C gs).length+u) (i-Γ.length-1)-Γ.length-1 =
            liftIndex ((repeated C gs).length+u) (i-Γ.length-1) := by omega
        rw [ha,ih]
        have hb : ¬ Γ.length+1+(i-Γ.length-1) < Γ.length := by omega
        have hd : Γ.length+1+(i-Γ.length-1) ≠ Γ.length := by omega
        rw [ite_eq_right hb,ite_eq_right hd]
        have heq : Γ.length+1+(i-Γ.length-1)-Γ.length-1 = i-Γ.length-1 := by omega
        rw [heq]
        have hcut : Γ.length+(gaps gs).length+1+u = Γ.length+((gaps gs).length+1+u) := by omega
        rw [hcut,liftIndex_add]

theorem copyIndex_interior_inserted (C E : NormalForm P)
    (pre post : List (List (NormalForm P))) (U V : List (NormalForm P)) :
    copyIndex (pre ++ (U ++ E :: V) :: post) (repeated C pre ++ U).length =
      (gaps pre ++ U).length := by
  induction pre with
  | nil =>
    simp only [List.nil_append,repeated,gaps,copyIndex,List.length_append,List.length_cons]
    rw [ite_eq_left (by omega : U.length < U.length + (V.length+1))]
  | cons Γ pre ih =>
    simp only [List.cons_append,repeated,gaps,List.length_append,List.length_cons] at *
    rw [copyIndex,ite_eq_right (by omega),ite_eq_right (by omega)]
    have he : Γ.length+((repeated C pre).length+1)+U.length-Γ.length-1 =
        (repeated C pre).length+U.length := by omega
    rw [he,ih]
    omega

theorem copyIndex_tail_inserted (C : NormalForm P) (gs : List (List (NormalForm P)))
    (u : Nat) : copyIndex gs ((repeated C gs).length+u) = (gaps gs).length+1+u := by
  induction gs with
  | nil => simp only [copyIndex,repeated,gaps,List.length_nil,Nat.zero_add]; omega
  | cons Γ gs ih =>
    simp only [repeated,gaps,List.length_append,List.length_cons]
    rw [copyIndex,ite_eq_right (by omega),ite_eq_right (by omega)]
    have he : Γ.length+((repeated C gs).length+1)+u-Γ.length-1 = (repeated C gs).length+u := by omega
    rw [he,ih]
    omega

theorem liftIndex_strict (k i j : Nat) (h : i < j) : liftIndex k i < liftIndex k j := by
  unfold liftIndex
  split <;> split <;> omega

end GapInsertion
end DosenPetric.Reduced.Gentzen
