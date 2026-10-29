module

public import DosenPetric.FormulaSubstitutionCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.FiniteBlocks

/-- Coordinates for a binary disjoint union, including empty summands. -/
def sumEncode {n m : Nat} : Sum (Fin n) (Fin m) → Fin (n+m)
  | .inl x => ⟨x.val,by have := x.isLt; omega⟩
  | .inr y => ⟨n+y.val,by have := y.isLt; omega⟩

def sumDecode {n m : Nat} (x : Fin (n+m)) : Sum (Fin n) (Fin m) :=
  if h : x.val < n then .inl ⟨x.val,h⟩
  else .inr ⟨x.val-n,by have := x.isLt; omega⟩

theorem sumDecode_encode {n m : Nat} (x : Sum (Fin n) (Fin m)) :
    sumDecode (sumEncode x) = x := by
  cases x with
  | inl x => simp [sumDecode,sumEncode,x.isLt]
  | inr y =>
    have hn : ¬ n+y.val < n := by omega
    simp [sumDecode,sumEncode,hn]

theorem sumEncode_decode {n m : Nat} (x : Fin (n+m)) :
    sumEncode (sumDecode x) = x := by
  unfold sumDecode
  split
  · apply Fin.ext; rfl
  · apply Fin.ext; simp only [sumEncode]; have := x.isLt; omega

def total : {m : Nat} → (Fin m → Nat) → Nat
  | 0,_ => 0
  | _+1,n => n 0 + total (fun i => n i.succ)

def prefixSum : {m : Nat} → (n : Fin m → Nat) → Fin m → Nat
  | 0,_,i => Fin.elim0 i
  | _+1,n,i => Fin.cases 0 (fun j => n 0 + prefixSum (fun k => n k.succ) j) i

abbrev Block {m : Nat} (n : Fin m → Nat) := (i : Fin m) × Fin (n i)

def encode : {m : Nat} → (n : Fin m → Nat) → Block n → Fin (total n)
  | 0,_,x => Fin.elim0 x.1
  | _+1,n,⟨i,t⟩ =>
    Fin.cases (fun t => sumEncode (.inl t))
      (fun j t => sumEncode (.inr (encode (fun k => n k.succ) ⟨j,t⟩))) i t

def decode : {m : Nat} → (n : Fin m → Nat) → Fin (total n) → Block n
  | 0,_,x => Fin.elim0 x
  | _+1,n,x =>
    match sumDecode x with
    | .inl t => ⟨0,t⟩
    | .inr t => let y := decode (fun k => n k.succ) t; ⟨y.1.succ,y.2⟩

theorem encode_value {m : Nat} (n : Fin m → Nat) (x : Block n) :
    (encode n x).val = prefixSum n x.1 + x.2.val := by
  induction m with
  | zero => exact Fin.elim0 x.1
  | succ m ih =>
    obtain ⟨i,t⟩ := x
    induction i using Fin.cases with
    | zero => simp only [encode,prefixSum,Fin.cases_zero,sumEncode,Nat.zero_add]
    | succ i =>
      change n 0 + (encode (fun k => n k.succ) ⟨i,t⟩).val =
        (n 0 + prefixSum (fun k => n k.succ) i) + t.val
      rw [ih]
      exact (Nat.add_assoc _ _ _).symm

theorem decode_encode {m : Nat} (n : Fin m → Nat) (x : Block n) :
    decode n (encode n x) = x := by
  induction m with
  | zero => exact Fin.elim0 x.1
  | succ m ih =>
    obtain ⟨i,t⟩ := x
    induction i using Fin.cases with
    | zero => simp only [encode,Fin.cases_zero,decode,sumDecode_encode]
    | succ i =>
      simp only [encode,Fin.cases_succ,decode,sumDecode_encode]
      rw [ih]

theorem encode_decode {m : Nat} (n : Fin m → Nat) (x : Fin (total n)) :
    encode n (decode n x) = x := by
  induction m with
  | zero => exact Fin.elim0 x
  | succ m ih =>
    have he := sumEncode_decode x
    simp only [decode]
    generalize hh : sumDecode x = y at he ⊢
    cases y with
    | inl t => exact he
    | inr t =>
      change sumEncode (.inr (encode (fun k => n k.succ) (decode (fun k => n k.succ) t))) = x
      rw [ih]
      exact he

end DosenPetric.FiniteBlocks
