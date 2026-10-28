module

public import DosenPetric.GentzenPrincipalConjunctionRule

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace LogicalHeadRouting

/-- Move the two consumed component tags below a fresh logical principal formula. -/
def components (F U : List (NormalForm P)) (A B C : NormalForm P) :
    ExchangeScript P (A :: B :: (At.shift F (.here C U)).erase) (F ++ A :: B :: U) :=
  (ExchangeScript.exchange [] F [A,B] U).reindex
    (by simp only [List.nil_append, List.cons_append]; rw [At.erase_shift])
    (by simp only [List.nil_append, List.append_assoc, List.cons_append])

theorem components_index (F U : List (NormalForm P)) (A B C : NormalForm P)
    {E : NormalForm P} (a : At (F ++ A :: B :: U) E) :
    ((components F U A B C).get a).index = exchangeIndex 0 F.length 2 a.index := by
  simp only [components, ExchangeScript.get, ExchangeScript.rewire, Rewire.get,
    At.index_cast, swapBlocks_index, List.length_nil, List.length_cons]

theorem first (F U : List (NormalForm P)) (A B C : NormalForm P) :
    (components F U A B C).get (At.shift F (.here A (B :: U))) =
      .here A (B :: (At.shift F (.here C U)).erase) := by
  apply At.index_injective
  rw [components_index, At.index_shift]
  simp only [At.index, Nat.add_zero, exchangeIndex, Nat.zero_add]
  split <;> (try split) <;> (try split) <;> omega

theorem second (F U : List (NormalForm P)) (A B C : NormalForm P) :
    (components F U A B C).get (At.shift F (.there (.here B U))) =
      .there (.here B (At.shift F (.here C U)).erase) := by
  apply At.index_injective
  rw [components_index, At.index_shift]
  simp only [At.index, exchangeIndex, Nat.zero_add]
  split <;> (try split) <;> (try split) <;> omega

theorem before {F : List (NormalForm P)} (U : List (NormalForm P)) (A B C : NormalForm P)
    {E : NormalForm P} (a : At F E) :
    (components F U A B C).get (a.before (A :: B :: U)) =
      .there (.there ((a.before U).cast (At.erase_shift F U C).symm)) := by
  apply At.index_injective
  rw [components_index, At.index_before]
  simp only [At.index, At.index_cast, At.index_before]
  have hi := a.index_lt
  unfold exchangeIndex
  split <;> (try split) <;> (try split) <;> omega

theorem tail (F U : List (NormalForm P)) (A B C : NormalForm P)
    {E : NormalForm P} (a : At U E) :
    (components F U A B C).get (At.shift F (.there (.there a))) =
      .there (.there ((At.shift F a).cast (At.erase_shift F U C).symm)) := by
  apply At.index_injective
  rw [components_index, At.index_shift]
  simp only [At.index, At.index_cast, At.index_shift]
  unfold exchangeIndex
  split <;> (try split) <;> (try split) <;> omega

theorem principal_prefix (F U : List (NormalForm P)) (C : NormalForm P)
    {E : NormalForm P} (a : At F E) :
    (At.shift F (.here C U)).toHead.get (a.before (C :: U)) =
      .there ((a.before U).cast (At.erase_shift F U C).symm) := by
  apply At.index_injective
  rw [At.toHead_get_index, At.index_shift, At.index_before]
  simp only [At.index, At.index_cast, At.index_before, Nat.add_zero]
  have hi := a.index_lt
  unfold exchangeIndex
  split <;> (try split) <;> (try split) <;> omega

theorem principal_tail (F U : List (NormalForm P)) (C : NormalForm P)
    {E : NormalForm P} (a : At U E) :
    (At.shift F (.here C U)).toHead.get (At.shift F (.there a)) =
      .there ((At.shift F a).cast (At.erase_shift F U C).symm) := by
  apply At.index_injective
  rw [At.toHead_get_index, At.index_shift]
  simp only [At.index, At.index_cast, At.index_shift, Nat.add_zero]
  unfold exchangeIndex
  split <;> (try split) <;> (try split) <;> omega

/-- The actual exchange square for a principal logical formula at any tagged gap. -/
theorem square (o : Op) (F U : List (NormalForm P)) (A B : NormalForm P) :
    (side P o).comp ((At.shift F (.here (o.formula A B) U)).toHead.arrow o)
        (logicalSide o F U A B) =
      (side P o).comp (logicalSide o [] (At.shift F (.here (o.formula A B) U)).erase A B)
        ((components F U A B (o.formula A B)).arrow o) := by
  let C := side P o
  apply side_ext o
  intro E a
  rw [C.assoc, C.assoc, ExchangeScript.component]
  cases At.cases_append F (A :: B :: U) a with
  | inl h =>
    obtain ⟨a,rfl⟩ := h
    rw [logical_prefix, ExchangeScript.component, principal_prefix, before]
    exact (logical_tail o [] _ A B _).symm
  | inr h =>
    obtain ⟨a,rfl⟩ := h
    cases a with
    | here =>
      rw [logical_first, ← C.assoc, ExchangeScript.component, At.toHead_get, first]
      exact (logical_first o [] _ A B).symm
    | there a => cases a with
      | here =>
        rw [logical_second, ← C.assoc, ExchangeScript.component, At.toHead_get, second]
        exact (logical_second o [] _ A B).symm
      | there a =>
        have hl : C.comp (logicalSide o F U A B)
            (component o (At.shift F (.there (.there a)))) =
            component o (At.shift F (.there a)) := by
          simpa only [At.shift] using logical_tail o F U A B a
        rw [hl, ExchangeScript.component, principal_tail, tail]
        exact (logical_tail o [] _ A B _).symm

end LogicalHeadRouting
end DosenPetric.Reduced.Gentzen
