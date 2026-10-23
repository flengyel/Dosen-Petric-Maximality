module

public import DosenPetric.GentzenFiberOrder

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- All selected upper contraction offsets, retaining multiplicity and order. -/
def copyOffsets : List (List (NormalForm P)) → List Nat
  | [] => []
  | Γ :: gs => Γ.length :: (copyOffsets gs).map (fun i => Γ.length + 1 + i)

theorem copyIndex_selected (gs : List (List (NormalForm P))) (i : Nat) :
    copyIndex gs i = (gaps gs).length ↔ i ∈ copyOffsets gs := by
  induction gs generalizing i with
  | nil => simp [copyIndex,gaps,copyOffsets]
  | cons Γ gs ih =>
    simp only [copyIndex,gaps,List.length_append,copyOffsets,List.mem_cons,List.mem_map]
    split
    · rename_i hi
      constructor
      · intro h; omega
      · rintro (h | ⟨j,_,hj⟩) <;> omega
    · split
      · rename_i hi
        subst i
        simp
      · rename_i hi hn
        constructor
        · intro h
          have hr : copyIndex gs (i - Γ.length - 1) = (gaps gs).length := by omega
          exact .inr ⟨i - Γ.length - 1,(ih _).mp hr,by omega⟩
        · rintro (h | ⟨j,hj,he⟩)
          · exact False.elim (hn h)
          · have hr := (ih j).mpr hj
            have he' : i - Γ.length - 1 = j := by omega
            rw [he',hr]

def copyHeadAt (C : NormalForm P) (Γ : List (NormalForm P))
    (gs : List (List (NormalForm P))) (Θ : List (NormalForm P)) : At (repeated C (Γ :: gs) ++ Θ) C :=
  (At.shift Γ (.here C (repeated C gs ++ Θ))).cast (copyTarget C Γ gs Θ)

def copyTailAt (C : NormalForm P) (Γ : List (NormalForm P))
    (gs : List (List (NormalForm P))) (Θ : List (NormalForm P)) {A : NormalForm P}
    (a : At (repeated C gs ++ Θ) A) : At (repeated C (Γ :: gs) ++ Θ) A :=
  (At.shift Γ a.there).cast (copyTarget C Γ gs Θ)

theorem copyHeadAt_index (C : NormalForm P) (Γ : List (NormalForm P))
    (gs : List (List (NormalForm P))) (Θ : List (NormalForm P)) :
    (copyHeadAt C Γ gs Θ).index = Γ.length := by
  simp only [copyHeadAt,At.index_cast,At.index_shift,At.index,Nat.add_zero]

theorem copyTailAt_index (C : NormalForm P) (Γ : List (NormalForm P))
    (gs : List (List (NormalForm P))) (Θ : List (NormalForm P)) {A : NormalForm P}
    (a : At (repeated C gs ++ Θ) A) :
    (copyTailAt C Γ gs Θ a).index = Γ.length + 1 + a.index := by
  simp only [copyTailAt,At.index_cast,At.index_shift,At.index]
  omega

def selectedCopies (C : NormalForm P) : (gs : List (List (NormalForm P))) →
    (Θ : List (NormalForm P)) → List (At (repeated C gs ++ Θ) C)
  | [], _ => []
  | Γ :: gs, Θ => copyHeadAt C Γ gs Θ :: (selectedCopies C gs Θ).map (copyTailAt C Γ gs Θ)

theorem selectedCopies_indices (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ : List (NormalForm P)) : (selectedCopies C gs Θ).map At.index = copyOffsets gs := by
  induction gs with
  | nil => rfl
  | cons Γ gs ih =>
    simp only [selectedCopies,List.map_cons,copyHeadAt_index,List.map_map,copyOffsets]
    rw [← ih,List.map_map]
    apply congrArg (List.cons Γ.length)
    apply List.map_congr_left
    intro a _
    exact copyTailAt_index C Γ gs Θ a

theorem selectedCopies_length (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ : List (NormalForm P)) : (selectedCopies C gs Θ).length = gs.length := by
  induction gs with
  | nil => rfl
  | cons Γ gs ih => simp only [selectedCopies,List.length_cons,List.length_map,ih]

theorem selectedCopies_mem (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ : List (NormalForm P)) (a : At (repeated C gs ++ Θ) C) :
    a ∈ selectedCopies C gs Θ ↔ a.index ∈ copyOffsets gs := by
  rw [← selectedCopies_indices C gs Θ,List.mem_map]
  constructor
  · intro h; exact ⟨a,h,rfl⟩
  · rintro ⟨b,hb,hi⟩
    cases At.index_injective b a hi
    exact hb

theorem selectedCopies_ordered (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ : List (NormalForm P)) : At.Ordered (selectedCopies C gs Θ) := by
  induction gs with
  | nil => exact .nil
  | cons Γ gs ih =>
    apply List.Pairwise.cons
    · intro a ha
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp ha
      rw [copyHeadAt_index,copyTailAt_index]
      omega
    · apply ih.map
      intro a b h
      rw [copyTailAt_index,copyTailAt_index]
      omega

theorem selectedCopies_nodup (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ : List (NormalForm P)) : (selectedCopies C gs Θ).Nodup := by
  apply (selectedCopies_ordered C gs Θ).imp
  intro a b h he
  cases he
  omega

/-- Every selected upper copy, and only those copies, is a predecessor. -/
theorem fiber_copies_selected (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ : List (NormalForm P)) :
    (TraceRoute.full (copies C gs Θ)).fiber (At.shift (gaps gs) (.here C Θ)) = selectedCopies C gs Θ := by
  apply At.ordered_ext _ _ (TraceRoute.fiber_ordered _ _) (selectedCopies_ordered C gs Θ)
  intro a
  rw [TraceRoute.fiber_correct,TraceRoute.get_full,Option.some.injEq,selectedCopies_mem]
  constructor
  · intro h
    have hi := congrArg At.index h
    simp only [copies_index,At.index_shift,At.index,Nat.add_zero] at hi
    exact (copyIndex_selected gs a.index).mp hi
  · intro h
    apply At.index_injective
    simp only [copies_index,At.index_shift,At.index,Nat.add_zero]
    exact (copyIndex_selected gs a.index).mpr h

/-- The unique upper offset above a noncontracted lower position. -/
def fixedCopyIndex : List (List (NormalForm P)) → Nat → Nat
  | [], i => i - 1
  | Γ :: gs, i => if i < Γ.length then i else Γ.length + 1 + fixedCopyIndex gs (i - Γ.length)

theorem copyIndex_fixed (gs : List (List (NormalForm P))) (i : Nat)
    (hi : i ≠ (gaps gs).length) : copyIndex gs (fixedCopyIndex gs i) = i := by
  induction gs generalizing i with
  | nil => simp only [gaps,List.length_nil] at hi; simp only [fixedCopyIndex,copyIndex]; omega
  | cons Γ gs ih =>
    simp only [gaps,List.length_append] at hi
    simp only [fixedCopyIndex]
    split
    · rename_i h; simp only [copyIndex,ite_eq_left h]
    · rename_i h
      have h₁ : ¬ Γ.length + 1 + fixedCopyIndex gs (i-Γ.length) < Γ.length := by omega
      have h₂ : Γ.length + 1 + fixedCopyIndex gs (i-Γ.length) ≠ Γ.length := by omega
      simp only [copyIndex,ite_eq_right h₁,ite_eq_right h₂]
      have he : Γ.length + 1 + fixedCopyIndex gs (i-Γ.length) - Γ.length - 1 = fixedCopyIndex gs (i-Γ.length) := by omega
      rw [he,ih (i-Γ.length) (by omega)]
      omega

theorem copyIndex_fixed_unique (gs : List (List (NormalForm P))) (i j : Nat)
    (hj : j ≠ (gaps gs).length) (h : copyIndex gs i = j) : i = fixedCopyIndex gs j := by
  induction gs generalizing i j with
  | nil => simp only [copyIndex,fixedCopyIndex] at *; omega
  | cons Γ gs ih =>
    simp only [gaps,List.length_append] at hj
    simp only [copyIndex] at h
    split at h
    · rename_i hi
      simp only [fixedCopyIndex,ite_eq_left (by omega : j < Γ.length)]
      exact h
    · rename_i hi
      split at h
      · omega
      · rename_i hn
        have hn' : j-Γ.length ≠ (gaps gs).length := by omega
        have hr : copyIndex gs (i-Γ.length-1) = j-Γ.length := by omega
        have hh := ih _ _ hn' hr
        simp only [fixedCopyIndex,ite_eq_right (by omega : ¬ j < Γ.length)]
        omega

namespace At

theorem splitAppend_left_index (Γ Δ : List (NormalForm P)) {A : NormalForm P}
    (a : At (Γ ++ Δ) A) (b : At Γ A) (h : splitAppend Γ Δ a = .inl b) : a.index = b.index := by
  cases cases_append Γ Δ a with
  | inl ha => obtain ⟨c,rfl⟩ := ha; rw [splitAppend_before] at h; cases h; exact index_before _ _
  | inr ha => obtain ⟨c,rfl⟩ := ha; rw [splitAppend_shift] at h; cases h

theorem splitAppend_right_index (Γ Δ : List (NormalForm P)) {A : NormalForm P}
    (a : At (Γ ++ Δ) A) (b : At Δ A) (h : splitAppend Γ Δ a = .inr b) : a.index = Γ.length + b.index := by
  cases cases_append Γ Δ a with
  | inl ha => obtain ⟨c,rfl⟩ := ha; rw [splitAppend_before] at h; cases h
  | inr ha => obtain ⟨c,rfl⟩ := ha; rw [splitAppend_shift] at h; cases h; exact index_shift _ _

end At

/-- The unique fixed upper position, computed from explicit gaps, not labels. -/
def fixedCopyAt (C : NormalForm P) : (gs : List (List (NormalForm P))) →
    (Θ : List (NormalForm P)) → {A : NormalForm P} →
    (a : At (gaps gs ++ C :: Θ) A) → a.index ≠ (gaps gs).length → At (repeated C gs ++ Θ) A
  | [], _, _, .here _ _, hn => False.elim (hn rfl)
  | [], _, _, .there a, _ => a
  | Γ :: gs, Θ, _, a, hn => by
    let b := a.cast (copySource C Γ gs Θ).symm
    have hb : b.index = a.index := At.index_cast _ _
    match h : At.splitAppend Γ (gaps gs ++ C :: Θ) b with
    | .inl c => exact (c.before (C :: (repeated C gs ++ Θ))).cast (copyTarget C Γ gs Θ)
    | .inr c =>
      have hc := At.splitAppend_right_index Γ (gaps gs ++ C :: Θ) b c h
      have hn' : c.index ≠ (gaps gs).length := by
        simp only [gaps,List.length_append] at hn
        omega
      exact copyTailAt C Γ gs Θ (fixedCopyAt C gs Θ c hn')

theorem fixedCopyAt_index (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ : List (NormalForm P)) {A : NormalForm P} (a : At (gaps gs ++ C :: Θ) A)
    (hn : a.index ≠ (gaps gs).length) : (fixedCopyAt C gs Θ a hn).index = fixedCopyIndex gs a.index := by
  induction gs with
  | nil =>
    cases a with
    | here => exact False.elim (hn rfl)
    | there a => simp only [fixedCopyAt,fixedCopyIndex,At.index,Nat.add_sub_cancel]
  | cons Γ gs ih =>
    let b := a.cast (copySource C Γ gs Θ).symm
    have hb : b.index = a.index := At.index_cast _ _
    simp only [fixedCopyAt]
    split
    · rename_i c hc
      have hi := At.splitAppend_left_index Γ (gaps gs ++ C :: Θ) b c hc
      have hl := c.index_lt
      simp only [At.index_cast,At.index_before,fixedCopyIndex,ite_eq_left (by omega : a.index < Γ.length)]
      omega
    · rename_i c hc
      have hi := At.splitAppend_right_index Γ (gaps gs ++ C :: Θ) b c hc
      rw [copyTailAt_index,ih]
      simp only [fixedCopyIndex,ite_eq_right (by omega : ¬ a.index < Γ.length)]
      have he : a.index - Γ.length = c.index := by omega
      rw [he]

theorem fiber_copies_fixed (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ : List (NormalForm P)) {A : NormalForm P} (x : At (gaps gs ++ C :: Θ) A)
    (hn : x.index ≠ (gaps gs).length) :
    (TraceRoute.full (copies C gs Θ)).fiber x = [fixedCopyAt C gs Θ x hn] := by
  apply TraceRoute.fiber_single
  intro y
  rw [TraceRoute.get_full,Option.some.injEq]
  constructor
  · intro h
    apply At.index_injective
    rw [fixedCopyAt_index]
    apply copyIndex_fixed_unique gs y.index x.index hn
    have hi := congrArg At.index h
    simpa only [copies_index] using hi
  · intro h
    cases h
    apply At.index_injective
    rw [copies_index,fixedCopyAt_index]
    exact copyIndex_fixed gs x.index hn

end DosenPetric.Reduced.Gentzen
