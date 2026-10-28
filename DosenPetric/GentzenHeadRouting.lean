module

public import DosenPetric.GentzenCrossComponents

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem split_before (o : Op) {F : List (NormalForm P)} (U : List (NormalForm P))
    {E : NormalForm P} (a : At F E) :
    (side P o).comp (split o F U)
      ((side P o).comp ((sideD P o).fst (fold o F) (fold o U)) (component o a)) =
      component o (a.before U) := by
  rw [← join_before, ← (side P o).assoc, split_join, (side P o).id_comp]

theorem split_shift (o : Op) (F : List (NormalForm P)) {U : List (NormalForm P)}
    {E : NormalForm P} (a : At U E) :
    (side P o).comp (split o F U)
      ((side P o).comp ((sideD P o).snd (fold o F) (fold o U)) (component o a)) =
      component o (At.shift F a) := by
  rw [← join_shift, ← (side P o).assoc, split_join, (side P o).id_comp]

namespace HeadRouting

/-- The selected head exchange with its residual list equality made explicit. -/
def front (F U : List (NormalForm P)) (A : NormalForm P) :
    ExchangeScript P (A :: (F ++ U)) (F ++ A :: U) :=
  (At.shift F (.here A U)).toHead.reindex
    (congrArg (fun xs => A :: xs) (At.erase_shift F U A)) rfl

theorem front_index (F U : List (NormalForm P)) (A : NormalForm P)
    {E : NormalForm P} (a : At (F ++ A :: U) E) :
    ((front F U A).get a).index = exchangeIndex 0 F.length 1 a.index := by
  change ((At.shift F (.here A U)).toHead.get a |>.cast _).index = _
  rw [At.index_cast, At.toHead_get_index, At.index_shift]
  rfl

theorem front_before {F : List (NormalForm P)} (U : List (NormalForm P))
    (A : NormalForm P) {E : NormalForm P} (a : At F E) :
    (front F U A).get (a.before (A :: U)) = .there (a.before U) := by
  apply At.index_injective
  rw [front_index, At.index_before]
  simp only [At.index, At.index_before]
  have hi := a.index_lt
  unfold exchangeIndex
  split <;> (try split) <;> (try split) <;> omega

theorem front_head (F U : List (NormalForm P)) (A : NormalForm P) :
    (front F U A).get (At.shift F (.here A U)) = .here A (F ++ U) := by
  apply At.index_injective
  rw [front_index, At.index_shift]
  simp only [At.index, Nat.add_zero, exchangeIndex, Nat.zero_add]
  split <;> (try split) <;> (try split) <;> omega

theorem front_tail (F U : List (NormalForm P)) (A : NormalForm P)
    {E : NormalForm P} (a : At U E) :
    (front F U A).get (At.shift F (.there a)) = .there (At.shift F a) := by
  apply At.index_injective
  rw [front_index, At.index_shift]
  simp only [At.index, At.index_shift]
  unfold exchangeIndex
  split <;> (try split) <;> (try split) <;> omega

/-- Every component of the actual selected exchange agrees with the cross diagram. -/
theorem front_arrow (o : Op) (F U : List (NormalForm P)) (A : NormalForm P) :
    (front F U A).arrow o =
      (side P o).comp ((sideM P o).tensor ((side P o).id A) (split o F U))
        ((side P o).comp ((sideM P o).cross A (fold o F) (fold o U))
          (join o F (A :: U))) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  apply side_ext o
  intro E a
  rw [ExchangeScript.component, C.assoc, C.assoc]
  cases At.cases_append F (A :: U) a with
  | inl h =>
    obtain ⟨a,rfl⟩ := h
    rw [front_before, component_there, join_before]
    rw [← C.assoc (M.cross A _ _), cross_first, C.assoc]
    rw [← C.assoc (M.tensor (C.id A) (split o F U)), ← D.snd_nat, C.assoc, split_before]
  | inr h =>
    obtain ⟨a,rfl⟩ := h
    cases a with
    | here =>
      rw [front_head, component_here, join_shift, component_here]
      rw [cross_second, ← D.fst_nat, C.comp_id]
    | there a =>
      rw [front_tail, component_there, join_shift, component_there]
      rw [← C.assoc (D.snd (fold o F) _), ← C.assoc (M.cross A _ _), cross_tail, C.assoc]
      rw [← C.assoc (M.tensor (C.id A) (split o F U)), ← D.snd_nat, C.assoc, split_shift]

/-- Remove the old fold comparison after moving the selected slot to the head. -/
theorem front_split (o : Op) (F U : List (NormalForm P)) (A : NormalForm P) :
    (side P o).comp ((front F U A).arrow o) (split o F (A :: U)) =
      (side P o).comp ((sideM P o).tensor ((side P o).id A) (split o F U))
        ((sideM P o).cross A (fold o F) (fold o U)) := by
  rw [front_arrow, (side P o).assoc, (side P o).assoc, join_split,
    (side P o).comp_id]

/-- For two leading slots the exact exchange is the monoidal cross. -/
theorem front_singleton (o : Op) (A B : NormalForm P) (U : List (NormalForm P)) :
    (front [A] U B).arrow o = (sideM P o).cross B A (fold o U) := by
  let C := side P o
  apply side_ext o
  intro E a
  rw [ExchangeScript.component]
  cases a with
  | here =>
    change component o ((front [A] U B).get (.here A (B :: U))) =
      C.comp ((sideM P o).cross B A (fold o U)) (component o (.here A (B :: U)))
    have hp : (front [A] U B).get (.here A (B :: U)) = .there (.here A U) := by
      simpa only [At.before, List.nil_append] using front_before U B (At.here A [])
    rw [hp, component_there, component_here, component_here]
    exact (cross_first o B A (fold o U)).symm
  | there a => cases a with
    | here =>
      change component o ((front [A] U B).get (.there (.here B U))) =
        C.comp ((sideM P o).cross B A (fold o U)) (component o (.there (.here B U)))
      have hp : (front [A] U B).get (.there (.here B U)) = .here B (A :: U) := by
        simpa only [At.shift, List.singleton_append] using front_head [A] U B
      rw [hp, component_here, component_there, component_here]
      exact (cross_second o B A (fold o U)).symm
    | there a =>
      change component o ((front [A] U B).get (.there (.there a))) =
        C.comp ((sideM P o).cross B A (fold o U)) (component o (.there (.there a)))
      have hp : (front [A] U B).get (.there (.there a)) = .there (.there a) := by
        simpa only [At.shift] using front_tail [A] U B a
      rw [hp]
      simp only [component_there]
      change C.comp ((sideD P o).snd B (o.formula A (fold o U)))
        (C.comp ((sideD P o).snd A (fold o U)) (component o a)) =
        C.comp ((sideM P o).cross B A (fold o U))
          (C.comp ((sideD P o).snd A (o.formula B (fold o U)))
            (C.comp ((sideD P o).snd B (fold o U)) (component o a)))
      have he := congrArg (fun k => C.comp k (component o a)) (cross_tail o B A (fold o U))
      cases o <;> dsimp only [C, side, category, opposite] at he ⊢
      all_goals simpa only [Laws.assoc] using he.symm

end HeadRouting
end DosenPetric.Reduced.Gentzen
