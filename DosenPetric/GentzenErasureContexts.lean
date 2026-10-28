module

public import DosenPetric.GentzenOppositeLogicalDescent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace At

theorem erase_before {F : List (NormalForm P)} {C : NormalForm P} (a : At F C)
    (U : List (NormalForm P)) : (a.before U).erase = a.erase ++ U := by
  induction a with
  | here => rfl
  | there a ih => exact congrArg (List.cons _) ih

theorem erase_shift_at (F : List (NormalForm P)) {U : List (NormalForm P)}
    {C : NormalForm P} (a : At U C) : (At.shift F a).erase = F ++ a.erase := by
  induction F with
  | nil => rfl
  | cons A F ih => exact congrArg (List.cons A) ih

theorem erase_shift_twice (F M : List (NormalForm P)) {U : List (NormalForm P)}
    {C : NormalForm P} (a : At U C) :
    (At.shift F (At.shift M a)).erase = F ++ (M ++ a.erase) :=
  (erase_shift_at F (At.shift M a)).trans (congrArg (fun xs => F ++ xs) (erase_shift_at M a))

theorem erase_length {F : List (NormalForm P)} {C : NormalForm P} (a : At F C) :
    a.erase.length + 1 = F.length := by
  induction a with
  | here => rfl
  | there a ih => simp only [erase,List.length_cons]; omega

end At
namespace LogicalDeletion

/-- Move a selected prefix tag to the head with a canonical residual append. -/
def headBefore {F : List (NormalForm P)} {C : NormalForm P} (a : At F C)
    (U : List (NormalForm P)) : ExchangeScript P (C :: (a.erase ++ U)) (F ++ U) :=
  (a.before U).toHead.reindex (congrArg (List.cons C) (a.erase_before U)) rfl

/-- Move a selected suffix tag to the head with a canonical residual prefix. -/
def headShift (F : List (NormalForm P)) {U : List (NormalForm P)} {C : NormalForm P}
    (a : At U C) : ExchangeScript P (C :: (F ++ a.erase)) (F ++ U) :=
  (At.shift F a).toHead.reindex (congrArg (List.cons C) (At.erase_shift_at F a)) rfl

theorem headBefore_index {F : List (NormalForm P)} {C : NormalForm P} (a : At F C)
    (U : List (NormalForm P)) {E : NormalForm P} (b : At (F ++ U) E) :
    ((headBefore a U).get b).index = exchangeIndex 0 a.index 1 b.index := by
  change (((a.before U).toHead.get b).cast _).index = _
  rw [At.index_cast,At.toHead_get_index,At.index_before]

theorem headShift_index (F : List (NormalForm P)) {U : List (NormalForm P)}
    {C : NormalForm P} (a : At U C) {E : NormalForm P} (b : At (F ++ U) E) :
    ((headShift F a).get b).index = exchangeIndex 0 (F.length + a.index) 1 b.index := by
  change (((At.shift F a).toHead.get b).cast _).index = _
  rw [At.index_cast,At.toHead_get_index,At.index_shift]

theorem headBefore_selected {F : List (NormalForm P)} {C : NormalForm P} (a : At F C)
    (U : List (NormalForm P)) : (headBefore a U).get (a.before U) = .here C (a.erase ++ U) := by
  apply At.index_injective
  rw [headBefore_index,At.index_before]
  simp only [At.index,exchangeIndex,Nat.zero_add]
  split <;> (try split) <;> (try split) <;> omega

theorem headBefore_fixed {F : List (NormalForm P)} {C E : NormalForm P} (a : At F C)
    (U : List (NormalForm P)) (b : At a.erase E) :
    (headBefore a U).get ((a.retain b).before U) = .there (b.before U) := by
  apply At.index_injective
  rw [headBefore_index,At.index_before,At.retain_index]
  simp only [At.index,At.index_before]
  unfold exchangeIndex
  split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem headBefore_tail {F U : List (NormalForm P)} {C E : NormalForm P}
    (a : At F C) (b : At U E) :
    (headBefore a U).get (At.shift F b) = .there (At.shift a.erase b) := by
  apply At.index_injective
  rw [headBefore_index,At.index_shift]
  simp only [At.index,At.index_shift]
  have hi := a.index_lt
  have hl := a.erase_length
  unfold exchangeIndex
  split <;> (try split) <;> (try split) <;> omega

theorem headShift_before (F : List (NormalForm P)) {U : List (NormalForm P)}
    {C E : NormalForm P} (a : At U C) (b : At F E) :
    (headShift F a).get (b.before U) = .there (b.before a.erase) := by
  apply At.index_injective
  rw [headShift_index,At.index_before]
  simp only [At.index,At.index_before]
  have hi := b.index_lt
  unfold exchangeIndex
  split <;> (try split) <;> (try split) <;> omega

theorem headShift_selected (F : List (NormalForm P)) {U : List (NormalForm P)}
    {C : NormalForm P} (a : At U C) :
    (headShift F a).get (At.shift F a) = .here C (F ++ a.erase) := by
  apply At.index_injective
  rw [headShift_index,At.index_shift]
  simp only [At.index,exchangeIndex,Nat.zero_add]
  split <;> (try split) <;> (try split) <;> omega

theorem headShift_fixed (F : List (NormalForm P)) {U : List (NormalForm P)}
    {C E : NormalForm P} (a : At U C) (b : At a.erase E) :
    (headShift F a).get (At.shift F (a.retain b)) = .there (At.shift F b) := by
  apply At.index_injective
  rw [headShift_index,At.index_shift,At.retain_index]
  simp only [At.index,At.index_shift]
  unfold exchangeIndex
  split <;> (try split) <;> (try split) <;> (try split) <;> omega

end LogicalDeletion
end DosenPetric.Reduced.Gentzen
