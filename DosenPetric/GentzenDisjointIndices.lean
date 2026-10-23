module

public import DosenPetric.GentzenContractionBlocks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.Disjoint
universe u
variable {P : Type u}

/-- Replace one fixed block by a smaller block, retaining an explicit map inside it. -/
def splice (k r s : Nat) (f : Nat → Nat) (i : Nat) : Nat :=
  if i < k then i else if i < k+r then k+f (i-k) else i-r+s

theorem splice_before (k r s : Nat) (f : Nat → Nat) (i : Nat) (h : i < k) :
    splice k r s f i = i := by simp only [splice,ite_eq_left h]
theorem splice_inside (k r s : Nat) (f : Nat → Nat) (i : Nat) (h : k ≤ i) (h' : i < k+r) :
    splice k r s f i = k+f (i-k) := by rw [splice,ite_eq_right (by omega),ite_eq_left h']
theorem splice_after (k r s : Nat) (f : Nat → Nat) (i : Nat) (h : k+r ≤ i) :
    splice k r s f i = i-r+s := by rw [splice,ite_eq_right (by omega),ite_eq_right (by omega)]
theorem splice_add (a k r s : Nat) (f : Nat → Nat) (i : Nat) :
    splice (a+k) r s f (a+i) = a+splice k r s f i := by
  by_cases h : i < k
  · rw [splice_before _ _ _ _ _ (by omega),splice_before _ _ _ _ _ h]
  · by_cases h' : i < k+r
    · rw [splice_inside _ _ _ _ _ (by omega) (by omega),splice_inside _ _ _ _ _ (by omega) h']
      have he : a+i-(a+k) = i-k := by omega
      rw [he]; omega
    · rw [splice_after _ _ _ _ _ (by omega),splice_after _ _ _ _ _ (by omega)]
      omega

theorem copy_tail (C : NormalForm P) (gs : List (List (NormalForm P))) (i : Nat)
    (hi : (repeated C gs).length ≤ i) : copyIndex gs i = (gaps gs).length+1+(i-(repeated C gs).length) := by
  induction gs generalizing i with
  | nil => simp only [copyIndex,gaps,repeated,List.length_nil]; omega
  | cons Γ gs ih =>
    simp only [repeated,List.length_append,List.length_cons] at hi ⊢
    have hh := ih (i-Γ.length-1) (by omega)
    rw [copyIndex,ite_eq_right (by omega),ite_eq_right (by omega),hh]
    omega

theorem copy_bound (C : NormalForm P) (gs : List (List (NormalForm P))) (i : Nat)
    (hi : i < (repeated C gs).length) : copyIndex gs i < (gaps gs).length+1 := by
  induction gs generalizing i with
  | nil => simp only [repeated,List.length_nil] at hi; omega
  | cons Γ gs ih =>
    simp only [repeated,List.length_append,List.length_cons] at hi
    simp only [gaps,List.length_append,copyIndex]
    split
    · omega
    · split
      · omega
      · have hh := ih (i-Γ.length-1) (by omega)
        omega

theorem copy_prefix (W H : List (NormalForm P)) (hs : List (List (NormalForm P))) (i : Nat) :
    copyIndex ((W++H)::hs) i = if i < W.length then i else W.length+copyIndex (H::hs) (i-W.length) := by
  have he : i-(W.length+H.length)-1 = i-W.length-H.length-1 := by omega
  simp only [copyIndex,List.length_append,he]
  repeat first | split | omega

theorem copy_splice (E : NormalForm P) (W H : List (NormalForm P))
    (hs : List (List (NormalForm P))) (i : Nat) :
    copyIndex ((W++H)::hs) i = splice W.length (repeated E (H::hs)).length
      ((gaps (H::hs)).length+1) (copyIndex (H::hs)) i := by
  rw [copy_prefix]
  unfold splice
  split
  · rfl
  · split
    · rfl
    · rename_i h₁ h₂
      rw [copy_tail E (H::hs) (i-W.length) (by omega)]
      omega

/-- Naturality of outer copies for an arbitrary map of a single fixed block. -/
theorem copy_splice_square (C : NormalForm P) (pre post : List (List (NormalForm P)))
    (U X Y V : List (NormalForm P)) (f : Nat → Nat)
    (hf : ∀ j, j < X.length → f j < Y.length) (i : Nat) :
    copyIndex (pre++(U++Y++V)::post)
      (splice (repeated C pre ++ U).length X.length Y.length f i) =
    splice (gaps pre ++ U).length X.length Y.length f
      (copyIndex (pre++(U++X++V)::post) i) := by
  induction pre generalizing i with
  | nil =>
    simp only [List.nil_append,repeated,List.nil_append]
    have hX : (U++X++V).length = U.length+X.length+V.length := by simp only [List.length_append]
    have hY : (U++Y++V).length = U.length+Y.length+V.length := by simp only [List.length_append]
    by_cases hp : i < U.length
    · rw [splice_before _ _ _ _ _ hp,copyIndex,ite_eq_left (by omega),
        copyIndex,ite_eq_left (by omega),splice_before _ _ _ _ _ hp]
    · by_cases hx : i < U.length+X.length
      · have h := hf (i-U.length) (by omega)
        rw [splice_inside _ _ _ _ _ (by omega) hx,copyIndex,ite_eq_left (by omega),
          copyIndex,ite_eq_left (by omega),splice_inside _ _ _ _ _ (by omega) hx]
      · rw [splice_after _ _ _ _ _ (by omega)]
        by_cases hv : i < U.length+X.length+V.length
        · rw [copyIndex,ite_eq_left (by omega),copyIndex,ite_eq_left (by omega),
            splice_after _ _ _ _ _ (by omega)]
        · by_cases he : i = U.length+X.length+V.length
          · rw [copyIndex,ite_eq_right (by omega),ite_eq_left (by omega),
              copyIndex,ite_eq_right (by omega),ite_eq_left (by omega),
              splice_after _ _ _ _ _ (by omega)]
            omega
          · rw [copyIndex,ite_eq_right (by omega),ite_eq_right (by omega),
              copyIndex,ite_eq_right (by omega),ite_eq_right (by omega)]
            rw [splice_after _ _ _ _ _ (by omega)]
            have harg : i-X.length+Y.length-(U++Y++V).length-1 = i-(U++X++V).length-1 := by omega
            rw [harg]; omega
  | cons Γ pre ih =>
    have hgX : (gaps (pre++(U++X++V)::post)).length =
        (gaps pre).length+U.length+X.length+V.length+(gaps post).length := by
      simp only [GapInsertion.gaps_append,gaps,List.length_append]; omega
    have hgY : (gaps (pre++(U++Y++V)::post)).length =
        (gaps pre).length+U.length+Y.length+V.length+(gaps post).length := by
      simp only [GapInsertion.gaps_append,gaps,List.length_append]; omega
    simp only [List.cons_append,repeated,gaps,List.length_append,List.length_cons]
    by_cases hp : i < Γ.length
    · rw [splice]
      rw [ite_eq_left (by omega),copyIndex,ite_eq_left hp,copyIndex,ite_eq_left hp]
      rw [splice,ite_eq_left (by omega)]
    · by_cases he : i = Γ.length
      · subst i
        rw [splice,ite_eq_left (by omega),copyIndex,ite_eq_right (Nat.lt_irrefl _),ite_eq_left rfl,
          copyIndex,ite_eq_right (Nat.lt_irrefl _),ite_eq_left rfl]
        rw [splice,ite_eq_right (by omega),ite_eq_right (by omega)]
        omega
      · have hi : i = Γ.length+1+(i-Γ.length-1) := by omega
        have hk : Γ.length+((repeated C pre).length+1)+U.length =
            (Γ.length+1)+((repeated C pre).length+U.length) := by omega
        have hl : Γ.length+(gaps pre).length+U.length = Γ.length+((gaps pre).length+U.length) := by omega
        have ih' := ih (i-Γ.length-1)
        simp only [List.length_append] at ih'
        rw [hk,hi,splice_add,GapLogical.copy_after,ih',GapLogical.copy_after,hl,splice_add]

end DosenPetric.Reduced.Gentzen.Disjoint
