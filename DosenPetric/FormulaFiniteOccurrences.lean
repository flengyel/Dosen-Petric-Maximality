module

public import DosenPetric.FiniteBlockLocator

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Formula
open FiniteBlocks
universe u
variable {P : Type u}

def occurrenceCount : Formula P → Nat
  | .var _ => 1
  | .top => 0
  | .bot => 0
  | .conj A B => A.occurrenceCount+B.occurrenceCount
  | .disj A B => A.occurrenceCount+B.occurrenceCount
  | .neg A => A.occurrenceCount

def occurrenceIndex : (A : Formula P) → A.Occ → Fin A.occurrenceCount
  | .var _,_ => ⟨0,Nat.zero_lt_succ 0⟩
  | .top,x => Empty.elim x
  | .bot,x => Empty.elim x
  | .conj A _,.inl x => sumEncode (.inl (A.occurrenceIndex x))
  | .conj _ B,.inr x => sumEncode (.inr (B.occurrenceIndex x))
  | .disj A _,.inl x => sumEncode (.inl (A.occurrenceIndex x))
  | .disj _ B,.inr x => sumEncode (.inr (B.occurrenceIndex x))
  | .neg A,x => A.occurrenceIndex x

def occurrenceAt : (A : Formula P) → Fin A.occurrenceCount → A.Occ
  | .var _,_ => ()
  | .top,x => Fin.elim0 x
  | .bot,x => Fin.elim0 x
  | .conj A B,x => match sumDecode x with
    | .inl i => .inl (A.occurrenceAt i)
    | .inr j => .inr (B.occurrenceAt j)
  | .disj A B,x => match sumDecode x with
    | .inl i => .inl (A.occurrenceAt i)
    | .inr j => .inr (B.occurrenceAt j)
  | .neg A,x => A.occurrenceAt x

theorem occurrenceAt_index (A : Formula P) (x : A.Occ) :
    A.occurrenceAt (A.occurrenceIndex x) = x := by
  induction A with
  | var p => cases x; rfl
  | top => exact Empty.elim x
  | bot => exact Empty.elim x
  | conj A B ih ih' | disj A B ih ih' =>
    cases x with
    | inl x => simp only [occurrenceIndex,occurrenceAt,sumDecode_encode,ih]
    | inr x => simp only [occurrenceIndex,occurrenceAt,sumDecode_encode,ih']
  | neg A ih => exact ih x

theorem occurrenceIndex_at (A : Formula P) (i : Fin A.occurrenceCount) :
    A.occurrenceIndex (A.occurrenceAt i) = i := by
  induction A with
  | var p =>
    apply Fin.ext
    have hi : i.val < 1 := i.isLt
    change 0=i.val
    omega
  | top => exact Fin.elim0 i
  | bot => exact Fin.elim0 i
  | conj A B ih ih' | disj A B ih ih' =>
    have he := sumEncode_decode i
    simp only [occurrenceAt]
    generalize hh : sumDecode i = y at he ⊢
    cases y with
    | inl j => simp only [occurrenceIndex,ih]; exact he
    | inr j => simp only [occurrenceIndex,ih']; exact he
  | neg A ih => exact ih i

/-- The finite occurrence profile reads labels in left-to-right order. -/
def profile (A : Formula P) (i : Fin A.occurrenceCount) : P := A.label (A.occurrenceAt i)

theorem profile_index (A : Formula P) (x : A.Occ) : A.profile (A.occurrenceIndex x) = A.label x := by
  simp only [profile,occurrenceAt_index]

end DosenPetric.Formula
