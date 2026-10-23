module

public import DosenPetric.GentzenInsertionRouting

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.GapExchange
universe u
variable {P : Type u}

theorem exchange_add (a g x y i : Nat) :
    exchangeIndex (a+g) x y (a+i) = a + exchangeIndex g x y i := by
  unfold exchangeIndex
  repeat first | split | omega

theorem exchange_inverse (g x y i : Nat) :
    exchangeIndex g y x (exchangeIndex g x y i) = i := by
  unfold exchangeIndex
  repeat first | split | omega

theorem exchange_outside (g x y i : Nat) (h : i < g ∨ g+x+y ≤ i) :
    exchangeIndex g x y i = i := by
  unfold exchangeIndex
  repeat first | split | omega

theorem exchange_prefix (a g x y i : Nat) (h : i < a) :
    exchangeIndex (a+g) x y i = i := by
  exact exchange_outside (a+g) x y i (.inl (by omega))

theorem exchange_ge (g x y i : Nat) (h : g ≤ i) : g ≤ exchangeIndex g x y i := by
  unfold exchangeIndex
  repeat first | split | omega

theorem gaps_length (pre post : List (List (NormalForm P))) (U X Y V : List (NormalForm P)) :
    (gaps (pre ++ (U ++ Y ++ X ++ V) :: post)).length =
      (gaps (pre ++ (U ++ X ++ Y ++ V) :: post)).length := by
  simp only [GapInsertion.gaps_append,gaps,List.length_append]
  omega

theorem lower_end_le (pre post : List (List (NormalForm P))) (U X Y V : List (NormalForm P)) :
    (gaps pre ++ U).length+X.length+Y.length ≤
      (gaps (pre ++ (U ++ X ++ Y ++ V) :: post)).length := by
  simp only [GapInsertion.gaps_append,gaps,List.length_append]
  omega

/-- The numerical copies/exchange square, including all four positional blocks. -/
theorem copyIndex_interior (C : NormalForm P) (pre post : List (List (NormalForm P)))
    (U X Y V : List (NormalForm P)) (i : Nat) :
    copyIndex (pre ++ (U ++ Y ++ X ++ V) :: post)
      (exchangeIndex (repeated C pre ++ U).length X.length Y.length i) =
    exchangeIndex (gaps pre ++ U).length X.length Y.length
      (copyIndex (pre ++ (U ++ X ++ Y ++ V) :: post) i) := by
  induction pre generalizing i with
  | nil =>
    simp only [List.nil_append,repeated,List.nil_append]
    simp only [copyIndex,List.length_append]
    have hl : U.length+Y.length+X.length+V.length = U.length+X.length+Y.length+V.length := by omega
    rw [hl]
    unfold exchangeIndex
    repeat first | split | omega
  | cons Γ pre ih =>
    have hl := gaps_length pre post U X Y V
    have hk := lower_end_le pre post U X Y V
    simp only [List.cons_append,repeated,gaps,List.length_append,List.length_cons] at *
    by_cases hi : i < Γ.length
    · rw [exchange_outside _ _ _ _ (.inl (by omega)),copyIndex,ite_eq_left hi,
        copyIndex,ite_eq_left hi,exchange_outside _ _ _ _ (.inl (by omega))]
    · by_cases he : i = Γ.length
      · subst i
        have hu : Γ.length < Γ.length + ((repeated C pre).length+1)+U.length := by omega
        rw [exchange_outside _ _ _ _ (.inl hu),copyIndex,ite_eq_right (Nat.lt_irrefl _),ite_eq_left rfl,
          copyIndex,ite_eq_right (Nat.lt_irrefl _),ite_eq_left rfl]
        rw [exchange_outside _ _ _ _ (.inr (by omega))]
        omega
      · have hi' : i = (Γ.length+1)+(i-Γ.length-1) := by omega
        have hc : Γ.length+((repeated C pre).length+1)+U.length =
            (Γ.length+1)+((repeated C pre).length+U.length) := by omega
        rw [hc,hi',exchange_add]
        simp only [copyIndex,ite_eq_right (by omega : ¬ Γ.length+1+
          exchangeIndex ((repeated C pre).length+U.length) X.length Y.length (i-Γ.length-1) < Γ.length),
          ite_eq_right (by omega : Γ.length+1+
          exchangeIndex ((repeated C pre).length+U.length) X.length Y.length (i-Γ.length-1) ≠ Γ.length)]
        have ha : Γ.length+1+exchangeIndex ((repeated C pre).length+U.length) X.length Y.length
            (i-Γ.length-1)-Γ.length-1 =
            exchangeIndex ((repeated C pre).length+U.length) X.length Y.length (i-Γ.length-1) := by omega
        rw [ha,ih]
        rw [ite_eq_right (by omega),ite_eq_right (by omega)]
        have hb : Γ.length+1+(i-Γ.length-1)-Γ.length-1 = i-Γ.length-1 := by omega
        rw [hb]
        have hc' : Γ.length+(gaps pre).length+U.length = Γ.length+((gaps pre).length+U.length) := by omega
        rw [hc',exchange_add]

theorem copyIndex_tail (C : NormalForm P) (gs : List (List (NormalForm P))) (u x y i : Nat) :
    copyIndex gs (exchangeIndex ((repeated C gs).length+u) x y i) =
      exchangeIndex ((gaps gs).length+1+u) x y (copyIndex gs i) := by
  induction gs generalizing i with
  | nil =>
    simp only [repeated,gaps,List.length_nil,Nat.zero_add,copyIndex]
    have h := exchange_add 1 u x y i
    simpa only [Nat.add_comm] using h.symm
  | cons Γ gs ih =>
    simp only [repeated,gaps,List.length_append,List.length_cons]
    by_cases hi : i < Γ.length
    · rw [exchange_outside _ _ _ _ (.inl (by omega)),copyIndex,ite_eq_left hi,
        exchange_outside _ _ _ _ (.inl (by omega))]
    · by_cases he : i = Γ.length
      · subst i
        rw [exchange_outside _ _ _ _ (.inl (by omega)),copyIndex,
          ite_eq_right (Nat.lt_irrefl _),ite_eq_left rfl,
          exchange_outside _ _ _ _ (.inl (by omega))]
      · have hi' : i = (Γ.length+1)+(i-Γ.length-1) := by omega
        have hc : Γ.length+((repeated C gs).length+1)+u =
            (Γ.length+1)+((repeated C gs).length+u) := by omega
        rw [hc,hi',exchange_add]
        rw [copyIndex,ite_eq_right (by omega),ite_eq_right (by omega)]
        have ha : Γ.length+1+exchangeIndex ((repeated C gs).length+u) x y (i-Γ.length-1)-Γ.length-1 =
          exchangeIndex ((repeated C gs).length+u) x y (i-Γ.length-1) := by omega
        rw [ha,ih,copyIndex,ite_eq_right (by omega),ite_eq_right (by omega)]
        have hb : Γ.length+1+(i-Γ.length-1)-Γ.length-1 = i-Γ.length-1 := by omega
        rw [hb]
        have hc' : Γ.length+(gaps gs).length+1+u = Γ.length+((gaps gs).length+1+u) := by omega
        rw [hc',exchange_add]

/-- Selected indices are outside the exchanged interval, not merely unequal labels. -/
theorem selected_interior_outside (C : NormalForm P) (pre post : List (List (NormalForm P)))
    (U X Y V : List (NormalForm P)) (i : Nat)
    (h : i ∈ copyOffsets (pre ++ (U ++ X ++ Y ++ V) :: post)) :
    i < (repeated C pre ++ U).length ∨ (repeated C pre ++ U).length+X.length+Y.length ≤ i := by
  induction pre generalizing i with
  | nil =>
    simp only [List.nil_append,copyOffsets,List.mem_cons,List.mem_map,List.length_append] at h
    simp only [repeated,List.nil_append]
    rcases h with h | ⟨j,_,h⟩ <;> omega
  | cons Γ pre ih =>
    simp only [List.cons_append,copyOffsets,List.mem_cons,List.mem_map] at h
    simp only [repeated,List.length_append,List.length_cons]
    rcases h with h | ⟨j,hj,h⟩
    · exact .inl (by omega)
    · have hh := ih j hj
      simp only [List.length_append] at hh
      omega

theorem selected_lt_repeated (C : NormalForm P) (gs : List (List (NormalForm P)))
    (i : Nat) (h : i ∈ copyOffsets gs) : i < (repeated C gs).length := by
  induction gs generalizing i with
  | nil => cases h
  | cons Γ gs ih =>
    simp only [copyOffsets,List.mem_cons,List.mem_map] at h
    simp only [repeated,List.length_append,List.length_cons]
    rcases h with h | ⟨j,hj,h⟩
    · omega
    · have hh := ih j hj; omega

end DosenPetric.Reduced.Gentzen.GapExchange
