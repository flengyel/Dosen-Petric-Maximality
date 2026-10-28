module

public import DosenPetric.GentzenStructuralPrefix

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace StructuralProgram
variable {F U : List (NormalForm P)}

/-- An actual exchange of two complete blocks, with explicit empty transports. -/
def swapBlocks (F U : List (NormalForm P)) : StructuralProgram P (U ++ F) (F ++ U) :=
  (StructuralProgram.exchange [] F U []).reindex
    (by simp only [List.nil_append, List.append_nil])
    (by simp only [List.nil_append, List.append_nil])

theorem swapBlocks_before (F U : List (NormalForm P)) {A : NormalForm P} (a : At F A) :
    (swapBlocks F U).get (a.before U) = At.shift U a := by
  apply At.index_injective
  simp only [swapBlocks, get, At.index_cast, swapBlocks_index, At.index_before,
    At.index_shift, List.length_nil]
  simp only [exchangeIndex, Nat.zero_add, Nat.not_lt_zero, ite_false]
  rw [ite_eq_left a.index_lt, Nat.add_comm]

theorem swapBlocks_shift (F U : List (NormalForm P)) {A : NormalForm P} (a : At U A) :
    (swapBlocks F U).get (At.shift F a) = a.before F := by
  apply At.index_injective
  simp only [swapBlocks, get, At.index_cast, swapBlocks_index, At.index_before,
    At.index_shift, List.length_nil]
  simp only [exchangeIndex, Nat.zero_add, Nat.not_lt_zero, ite_false]
  have hi := a.index_lt
  split <;> (try split) <;> omega

/-- Extend a structural program through a fixed suffix using actual exchanges. -/
def suffixFixed (p : StructuralProgram P F U) (Δ : List (NormalForm P)) :
    StructuralProgram P (F ++ Δ) (U ++ Δ) :=
  .seq (swapBlocks Δ F) (.seq (p.prefixFixed Δ) (swapBlocks U Δ))

theorem suffixFixed_before (p : StructuralProgram P F U) (Δ : List (NormalForm P))
    {A : NormalForm P} (a : At U A) :
    (p.suffixFixed Δ).get (a.before Δ) = (p.get a).before Δ := by
  change (swapBlocks Δ F).get ((p.prefixFixed Δ).get ((swapBlocks U Δ).get (a.before Δ))) = _
  rw [swapBlocks_before, prefixFixed_shift, swapBlocks_shift]

theorem suffixFixed_shift (p : StructuralProgram P F U) (Δ : List (NormalForm P))
    {A : NormalForm P} (a : At Δ A) :
    (p.suffixFixed Δ).get (At.shift U a) = At.shift F a := by
  change (swapBlocks Δ F).get ((p.prefixFixed Δ).get ((swapBlocks U Δ).get (At.shift U a))) = _
  rw [swapBlocks_shift, prefixFixed_before, swapBlocks_before]

theorem suffixFixed_atomic (p : StructuralProgram P F U) (Δ : List (NormalForm P))
    (hp : p.Atomic) : (p.suffixFixed Δ).Atomic :=
  ⟨True.intro, prefixFixed_atomic p Δ hp, True.intro⟩

theorem suffixFixed_join (p : StructuralProgram P F U) (o : Op) (Δ : List (NormalForm P)) :
    (side P o).comp (join o F Δ) ((p.suffixFixed Δ).arrow o) =
      (side P o).comp ((sideM P o).tensor (p.arrow o) ((side P o).id (fold o Δ)))
        (join o U Δ) := by
  let C := side P o
  let D := sideD P o
  apply side_ext o
  intro A a
  cases At.cases_append U Δ a with
  | inl h =>
    obtain ⟨a,rfl⟩ := h
    rw [C.assoc, component, suffixFixed_before, join_before,
      C.assoc, join_before, ← C.assoc, ← D.fst_nat, C.assoc, component]
  | inr h =>
    obtain ⟨a,rfl⟩ := h
    rw [C.assoc, component, suffixFixed_shift, join_shift,
      C.assoc, join_shift, ← C.assoc, ← D.snd_nat, C.comp_id]

theorem suffixFixed_split (p : StructuralProgram P F U) (o : Op) (Δ : List (NormalForm P)) :
    (side P o).comp ((p.suffixFixed Δ).arrow o) (split o U Δ) =
      (side P o).comp (split o F Δ)
        ((sideM P o).tensor (p.arrow o) ((side P o).id (fold o Δ))) := by
  let C := side P o
  apply DiagonalData.cancel_left (C := C) _ _ (join o F Δ) (split o F Δ) (split_join o F Δ)
  rw [← C.assoc, suffixFixed_join, C.assoc, join_split, C.comp_id,
    ← C.assoc, join_split, C.id_comp]

end StructuralProgram
end DosenPetric.Reduced.Gentzen
