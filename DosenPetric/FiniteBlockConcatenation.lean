module

public import DosenPetric.FiniteBlockLocator

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.FiniteBlocks

variable {n m : Nat}

theorem sumDecode_zero (n m : Nat) : sumDecode (n:=n+1) (m:=m) 0 = .inl 0 := by
  unfold sumDecode
  rw [dite_eq_left (show (0 : Fin (n+1+m)).val < n+1 from Nat.zero_lt_succ n)]
  apply congrArg Sum.inl
  apply Fin.ext
  rfl

theorem sumDecode_succ (x : Fin (n+m)) :
    sumDecode (n:=n+1) (m:=m) ⟨x.val+1,by have := x.isLt; omega⟩ =
      match sumDecode (n:=n) (m:=m) x with
      | .inl i => .inl i.succ
      | .inr j => .inr j := by
  unfold sumDecode
  by_cases h : x.val < n
  · have h' : x.val+1 < n+1 := by omega
    rw [dite_eq_left h,dite_eq_left h']
    apply congrArg Sum.inl
    apply Fin.ext
    rfl
  · have h' : ¬ x.val+1 < n+1 := by omega
    rw [dite_eq_right h,dite_eq_right h']
    apply congrArg Sum.inr
    apply Fin.ext
    change x.val+1-(n+1) = x.val-n
    omega

def reindex {N M : Nat} (h : N = M) (f : Fin N → Nat) (i : Fin M) : Nat :=
  f (Fin.cast h.symm i)

theorem total_reindex {N M : Nat} (h : N = M) (f : Fin N → Nat) :
    total (reindex h f) = total f := by cases h; rfl

theorem prefix_reindex {N M : Nat} (h : N = M) (f : Fin N → Nat) (i : Fin N) :
    prefixSum (reindex h f) (Fin.cast h i) = prefixSum f i := by cases h; rfl

def concat (a : Fin n → Nat) (b : Fin m → Nat) (x : Fin (n+m)) : Nat :=
  match sumDecode x with
  | .inl i => a i
  | .inr j => b j

theorem concat_empty (a : Fin 0 → Nat) (b : Fin m → Nat) :
    reindex (Nat.zero_add m) (concat a b) = b := by
  funext x
  simp only [reindex,concat,sumDecode]
  rw [dite_eq_right (show ¬ (Fin.cast (Nat.zero_add m).symm x).val < 0 from Nat.not_lt_zero _)]
  congr 1

theorem concat_head (a : Fin (n+1) → Nat) (b : Fin m → Nat) : concat a b 0 = a 0 := by
  simp only [concat,sumDecode_zero]

theorem concat_tail (a : Fin (n+1) → Nat) (b : Fin m → Nat) :
    (fun i : Fin (n+m) => concat a b ⟨i.val+1,by have := i.isLt; omega⟩) =
      concat (fun i => a i.succ) b := by
  funext i
  simp only [concat,sumDecode_succ]
  cases sumDecode i <;> rfl

theorem concat_reindex_head (a : Fin (n+1) → Nat) (b : Fin m → Nat)
    (h : n+1+m = (n+m)+1) : reindex h (concat a b) 0 = a 0 := by
  change concat a b (Fin.cast h.symm 0) = a 0
  have hz : Fin.cast h.symm 0 = 0 := by apply Fin.ext; rfl
  rw [hz,concat_head]

theorem concat_reindex_tail (a : Fin (n+1) → Nat) (b : Fin m → Nat)
    (h : n+1+m = (n+m)+1) :
    (fun i : Fin (n+m) => reindex h (concat a b) i.succ) = concat (fun i => a i.succ) b := by
  exact concat_tail a b

theorem total_concat (a : Fin n → Nat) (b : Fin m → Nat) : total (concat a b) = total a+total b := by
  induction n with
  | zero =>
    rw [← total_reindex (Nat.zero_add m),concat_empty]
    change total b = 0+total b
    omega
  | succ n ih =>
    let h : n+1+m = (n+m)+1 := by omega
    rw [← total_reindex h]
    change reindex h (concat a b) 0 + total (fun i => reindex h (concat a b) i.succ) =
      a 0 + total (fun i => a i.succ) + total b
    rw [concat_reindex_head,concat_reindex_tail,ih,Nat.add_assoc]

theorem prefix_concat_left (a : Fin n → Nat) (b : Fin m → Nat) (i : Fin n) :
    prefixSum (concat a b) (sumEncode (.inl i)) = prefixSum a i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    let h : n+1+m = (n+m)+1 := by omega
    rw [← prefix_reindex h]
    induction i using Fin.cases with
    | zero =>
      have hz : Fin.cast h (sumEncode (.inl (0 : Fin (n+1)) : Sum (Fin (n+1)) (Fin m))) = 0 := by
        apply Fin.ext; rfl
      rw [hz,prefixSum_zero,prefixSum_zero]
    | succ i =>
      have hs : Fin.cast h (sumEncode (.inl i.succ : Sum (Fin (n+1)) (Fin m))) =
          (sumEncode (.inl i : Sum (Fin n) (Fin m))).succ := by apply Fin.ext; rfl
      rw [hs,prefixSum_succ,prefixSum_succ,concat_reindex_head,concat_reindex_tail,ih]

theorem prefix_concat_right (a : Fin n → Nat) (b : Fin m → Nat) (j : Fin m) :
    prefixSum (concat a b) (sumEncode (.inr j)) = total a + prefixSum b j := by
  induction n with
  | zero =>
    rw [← prefix_reindex (Nat.zero_add m),concat_empty]
    have hj : Fin.cast (Nat.zero_add m) (sumEncode (.inr j : Sum (Fin 0) (Fin m))) = j := by
      apply Fin.ext
      change 0+j.val=j.val
      omega
    rw [hj]
    change prefixSum b j = 0+prefixSum b j
    omega
  | succ n ih =>
    let h : n+1+m = (n+m)+1 := by omega
    rw [← prefix_reindex h]
    have hs : Fin.cast h (sumEncode (.inr j : Sum (Fin (n+1)) (Fin m))) =
        (sumEncode (.inr j : Sum (Fin n) (Fin m))).succ := by
      apply Fin.ext
      change n+1+j.val=(n+j.val)+1
      omega
    rw [hs,prefixSum_succ,concat_reindex_head,concat_reindex_tail,ih]
    change a 0 + (total (fun i => a i.succ) + prefixSum b j) =
      (a 0 + total (fun i => a i.succ)) + prefixSum b j
    omega

end DosenPetric.FiniteBlocks
