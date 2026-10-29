module

public import DosenPetric.FiniteBlockCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.FiniteBlocks

variable {m : Nat} (n : Fin m → Nat)

theorem encode_injective {x y : Block n} (h : encode n x = encode n y) : x = y := by
  have he := congrArg (decode n) h
  rw [decode_encode,decode_encode] at he
  exact he

theorem encode_surjective (x : Fin (total n)) : ∃ y : Block n, encode n y = x :=
  ⟨decode n x,encode_decode n x⟩

theorem prefixSum_zero {k : Nat} (n : Fin (k+1) → Nat) : prefixSum n 0 = 0 := by
  simp only [prefixSum,Fin.cases_zero]

theorem prefixSum_succ {k : Nat} (n : Fin (k+1) → Nat) (i : Fin k) :
    prefixSum n i.succ = n 0 + prefixSum (fun j => n j.succ) i := by
  simp only [prefixSum,Fin.cases_succ]

theorem prefix_length_le (i : Fin m) : prefixSum n i + n i ≤ total n := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    induction i using Fin.cases with
    | zero => simp only [prefixSum_zero,total]; omega
    | succ i =>
      rw [prefixSum_succ]
      have he := ih (fun j => n j.succ) i
      change n 0 + prefixSum (fun j => n j.succ) i + n i.succ ≤
        n 0 + total (fun j => n j.succ)
      omega

/-- The decoder locates the unique nonempty block containing a position. -/
theorem locator_bounds (x : Fin (total n)) :
    prefixSum n (decode n x).1 ≤ x.val ∧
    x.val < prefixSum n (decode n x).1 + n (decode n x).1 := by
  have he := encode_value n (decode n x)
  rw [encode_decode] at he
  have ht := (decode n x).2.isLt
  omega

theorem locator_unique (x : Fin (total n)) (i : Fin m)
    (lo : prefixSum n i ≤ x.val) (hi : x.val < prefixSum n i + n i) :
    (decode n x).1 = i := by
  let t : Fin (n i) := ⟨x.val-prefixSum n i,by omega⟩
  have he : encode n ⟨i,t⟩ = x := by
    apply Fin.ext
    rw [encode_value]
    change prefixSum n i + (x.val-prefixSum n i) = x.val
    omega
  rw [← he,decode_encode]

theorem zero_block_has_no_position (i : Fin m) (h : n i = 0) :
    ¬ ∃ x : Fin (total n), prefixSum n i ≤ x.val ∧ x.val < prefixSum n i + n i := by
  intro ⟨x,lo,hi⟩
  rw [h] at hi
  omega

/-- Translate zero-based Fin coordinates to the manuscript's {1,...,N}. -/
def oneBased {N : Nat} (x : Fin N) : {t : Nat // 0 < t ∧ t ≤ N} :=
  ⟨x.val+1,by have := x.isLt; omega⟩

def zeroBased {N : Nat} (x : {t : Nat // 0 < t ∧ t ≤ N}) : Fin N :=
  ⟨x.val-1,by have := x.property; omega⟩

theorem zeroBased_oneBased {N : Nat} (x : Fin N) : zeroBased (oneBased x) = x := by
  apply Fin.ext
  simp only [zeroBased,oneBased,Nat.add_sub_cancel]

theorem oneBased_zeroBased {N : Nat} (x : {t : Nat // 0 < t ∧ t ≤ N}) :
    oneBased (zeroBased x) = x := by
  apply Subtype.ext
  change x.val-1+1=x.val
  have := x.property
  omega

theorem encode_oneBased (x : Block n) :
    (oneBased (encode n x)).val = prefixSum n x.1 + (oneBased x.2).val := by
  change (encode n x).val+1 = prefixSum n x.1 + (x.2.val+1)
  rw [encode_value,Nat.add_assoc]

theorem locator_oneBased (x : Fin (total n)) :
    prefixSum n (decode n x).1 < (oneBased x).val ∧
    (oneBased x).val ≤ prefixSum n (decode n x).1 + n (decode n x).1 := by
  have he := locator_bounds n x
  change _ < x.val+1 ∧ x.val+1 ≤ _
  omega

end DosenPetric.FiniteBlocks
