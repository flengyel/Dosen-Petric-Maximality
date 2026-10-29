module

public import DosenPetric.ReducedDualSyntax

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.NormalForm
universe u
variable {P : Type u}

/-- Duality preserves every position tag while reversing its literal sign. -/
def toDual : (A : NormalForm P) → A.formula.Occ → A.dual.formula.Occ
  | .lit l,x => by cases l <;> exact x
  | .top,x => nomatch x
  | .bot,x => nomatch x
  | .conj A _,.inl x => .inl (toDual A x)
  | .conj _ B,.inr x => .inr (toDual B x)
  | .disj A _,.inl x => .inl (toDual A x)
  | .disj _ B,.inr x => .inr (toDual B x)

def fromDual : (A : NormalForm P) → A.dual.formula.Occ → A.formula.Occ
  | .lit l,x => by cases l <;> exact x
  | .top,x => nomatch x
  | .bot,x => nomatch x
  | .conj A _,.inl x => .inl (fromDual A x)
  | .conj _ B,.inr x => .inr (fromDual B x)
  | .disj A _,.inl x => .inl (fromDual A x)
  | .disj _ B,.inr x => .inr (fromDual B x)

theorem from_toDual (A : NormalForm P) (x : A.formula.Occ) : fromDual A (toDual A x) = x := by
  induction A with
  | lit l => cases l <;> rfl
  | top => cases x
  | bot => cases x
  | conj A B ih ih' => cases x <;> simp only [toDual,fromDual,ih,ih'] <;> rfl
  | disj A B ih ih' => cases x <;> simp only [toDual,fromDual,ih,ih'] <;> rfl

theorem to_fromDual (A : NormalForm P) (x : A.dual.formula.Occ) : toDual A (fromDual A x) = x := by
  induction A with
  | lit l => cases l <;> rfl
  | top => cases x
  | bot => cases x
  | conj A B ih ih' => cases x <;> simp only [toDual,fromDual,ih,ih'] <;> rfl
  | disj A B ih ih' => cases x <;> simp only [toDual,fromDual,ih,ih'] <;> rfl

theorem toDual_eq_iff (A : NormalForm P) (x y : A.formula.Occ) : toDual A x = toDual A y ↔ x = y := by
  constructor
  · intro h
    have hh := congrArg (fromDual A) h
    simpa only [from_toDual] using hh
  · intro h; cases h; rfl

theorem toDual_literal (A : NormalForm P) (x : A.formula.Occ) :
    A.dual.literalAt (toDual A x) = (A.literalAt x).flip := by
  induction A with
  | lit l => cases l <;> rfl
  | top => cases x
  | bot => cases x
  | conj A B ih ih' => cases x <;> simp only [dual,toDual,literalAt,ih,ih']
  | disj A B ih ih' => cases x <;> simp only [dual,toDual,literalAt,ih,ih']

end DosenPetric.NormalForm
