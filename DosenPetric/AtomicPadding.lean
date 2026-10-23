module

public import DosenPetric.AtomicPorts

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}
namespace AtomicPorts

/-- An occurrence decision, not a comparison of variable names. -/
inductive Selection (P : Type u) where
  | keep (p : P)
  | absent (p : P)

namespace Selection

@[reducible] def all : List (Selection P) → List P
  | [] => []
  | .keep p :: xs => p :: all xs
  | .absent p :: xs => p :: all xs

@[reducible] def kept : List (Selection P) → List P
  | [] => []
  | .keep p :: xs => p :: kept xs
  | .absent _ :: xs => kept xs

end Selection

/-- The source's h-conjunction, with the structural accumulator explicitly typed. -/
def inputPad {A B : NormalForm P} (f : Term P A B) : (xs : List (Selection P)) →
    Term P (expand .conj A (Selection.all xs)) (expand .conj B (Selection.kept xs))
  | [] => f
  | .keep p :: xs => inputPad (.tensor .conj f (.id (Atomic.etaObject p))) xs
  | .absent p :: xs => inputPad (.comp (.fst A (Atomic.etaObject p)) f) xs

/-- The source's h-disjunction; the kept identity is at q AND neg q. -/
def outputPad {A B : NormalForm P} (f : Term P A B) : (xs : List (Selection P)) →
    Term P (expand .disj A (Selection.kept xs)) (expand .disj B (Selection.all xs))
  | [] => f
  | .keep p :: xs => outputPad (.tensor .disj f (.id (Atomic.epsilonObject p))) xs
  | .absent p :: xs => outputPad (.comp f (.inl B (Atomic.epsilonObject p))) xs

theorem inputPad_positive {A B : NormalForm P} (f : Term P A B) (hf : f.Positive) (xs : List (Selection P)) :
    (inputPad f xs).Positive := by
  induction xs generalizing A B with
  | nil => exact hf
  | cons s xs ih =>
    cases s with
    | keep p => exact ih _ (.tensor _ hf (.id _))
    | absent p => exact ih _ (.comp (.fst ..) hf)

theorem outputPad_positive {A B : NormalForm P} (f : Term P A B) (hf : f.Positive) (xs : List (Selection P)) :
    (outputPad f xs).Positive := by
  induction xs generalizing A B with
  | nil => exact hf
  | cons s xs ih =>
    cases s with
    | keep p => exact ih _ (.tensor _ hf (.id _))
    | absent p => exact ih _ (.comp hf (.inl ..))

theorem etaOne_fst (A : NormalForm P) (p : P) :
    comp (ofTerm (etaOne A p)) (fst A (Atomic.etaObject p)) = id A := by
  change comp (comp (rightIn .conj A) (tensor .conj (id A) (ofTerm (.eta p)))) _ = _
  rw [Laws.assoc, ← Laws.fst_nat, Laws.comp_id, Laws.fst_top, Laws.rightIn_Out]

theorem inl_epsilonOne (A : NormalForm P) (p : P) :
    comp (inl A (Atomic.epsilonObject p)) (ofTerm (epsilonOne A p)) = id A := by
  change comp _ (comp (tensor .disj (id A) (ofTerm (.epsilon p))) (rightOut .disj A)) = _
  rw [← Laws.assoc, Laws.inl_nat, Laws.id_comp, Laws.inl_bot, Laws.rightIn_Out]

theorem inputPad_natural {A B : NormalForm P} (f : Term P A B) (xs : List (Selection P)) :
    comp (ofTerm (etaPrefix A (Selection.all xs))) (ofTerm (inputPad f xs)) =
      comp (ofTerm f) (ofTerm (etaPrefix B (Selection.kept xs))) := by
  induction xs generalizing A B with
  | nil => change comp (id A) (ofTerm f) = comp (ofTerm f) (id B); rw [Laws.id_comp, Laws.comp_id]
  | cons s xs ih =>
    cases s with
    | keep p =>
      change comp (comp (ofTerm (etaOne A p)) (ofTerm (etaPrefix _ (Selection.all xs))))
        (ofTerm (inputPad (.tensor .conj f (.id (Atomic.etaObject p))) xs)) = _
      rw [Laws.assoc, ih, ofTerm_tensor, ofTerm_id, ← Laws.assoc, etaOne_nat, Laws.assoc]
      rfl
    | absent p =>
      change comp (comp (ofTerm (etaOne A p)) (ofTerm (etaPrefix _ (Selection.all xs))))
        (ofTerm (inputPad (.comp (.fst A (Atomic.etaObject p)) f) xs)) = _
      rw [Laws.assoc, ih]
      simp only [ofTerm_comp, Laws.assoc]
      have hk : ofTerm (.fst A (Atomic.etaObject p)) = fst A (Atomic.etaObject p) := rfl
      rw [hk, ← Laws.assoc (ofTerm (etaOne A p)) (fst A (Atomic.etaObject p)), etaOne_fst, Laws.id_comp]

theorem outputPad_natural {A B : NormalForm P} (f : Term P A B) (xs : List (Selection P)) :
    comp (ofTerm (outputPad f xs)) (ofTerm (epsilonSuffix B (Selection.all xs))) =
      comp (ofTerm (epsilonSuffix A (Selection.kept xs))) (ofTerm f) := by
  induction xs generalizing A B with
  | nil => change comp (ofTerm f) (id B) = comp (id A) (ofTerm f); rw [Laws.comp_id, Laws.id_comp]
  | cons s xs ih =>
    cases s with
    | keep p =>
      change comp (ofTerm (outputPad (.tensor .disj f (.id (Atomic.epsilonObject p))) xs))
        (comp (ofTerm (epsilonSuffix _ (Selection.all xs))) (ofTerm (epsilonOne B p))) = _
      rw [← Laws.assoc, ih, ofTerm_tensor, ofTerm_id, Laws.assoc, epsilonOne_nat, ← Laws.assoc]
      rfl
    | absent p =>
      change comp (ofTerm (outputPad (.comp f (.inl B (Atomic.epsilonObject p))) xs))
        (comp (ofTerm (epsilonSuffix _ (Selection.all xs))) (ofTerm (epsilonOne B p))) = _
      rw [← Laws.assoc, ih]
      simp only [ofTerm_comp, Laws.assoc]
      have hk : ofTerm (.inl B (Atomic.epsilonObject p)) = inl B (Atomic.epsilonObject p) := rfl
      rw [hk, inl_epsilonOne, Laws.comp_id]

theorem expand_append (o : Op) (A : NormalForm P) (ps qs : List P) :
    expand o A (ps ++ qs) = expand o (expand o A ps) qs := by
  induction ps generalizing A with
  | nil => rfl
  | cons p ps ih => exact ih (o.formula A (block o p))

end AtomicPorts
end DosenPetric.Reduced
