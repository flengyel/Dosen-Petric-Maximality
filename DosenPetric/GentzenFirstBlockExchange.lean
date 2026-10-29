module

public import DosenPetric.GentzenConjSecondCore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryMix

theorem swapBlocks_before (F U K : List (NormalForm P)) {A : NormalForm P} (a : At F A) :
    (swapBlocks F U K).get (a.before (U ++ K)) = At.shift U (a.before K) := by
  apply At.index_injective
  simp only [swapBlocks,ExchangeScript.get,ExchangeScript.rewire,Rewire.get,
    At.index_cast,swapBlocks_index,At.index_before,At.index_shift,List.length_nil]
  have hi := a.index_lt
  unfold exchangeIndex
  repeat first | split | omega

theorem swapBlocks_middle (F U K : List (NormalForm P)) {A : NormalForm P} (a : At U A) :
    (swapBlocks F U K).get (At.shift F (a.before K)) = a.before (F ++ K) := by
  apply At.index_injective
  simp only [swapBlocks,ExchangeScript.get,ExchangeScript.rewire,Rewire.get,
    At.index_cast,swapBlocks_index,At.index_before,At.index_shift,List.length_nil]
  have hi := a.index_lt
  unfold exchangeIndex
  repeat first | split | omega

theorem swapBlocks_tail (F U K : List (NormalForm P)) {A : NormalForm P} (a : At K A) :
    (swapBlocks F U K).get (At.shift F (At.shift U a)) = At.shift U (At.shift F a) := by
  apply At.index_injective
  simp only [swapBlocks,ExchangeScript.get,ExchangeScript.rewire,Rewire.get,
    At.index_cast,swapBlocks_index,At.index_shift,List.length_nil]
  have hi := a.index_lt
  unfold exchangeIndex
  repeat first | split | omega

theorem swapBlocks_arrow (o : Op) (F U K : List (NormalForm P)) :
    (swapBlocks F U K).arrow o =
      (side P o).comp (split o U (F ++ K))
        ((side P o).comp ((sideM P o).tensor ((side P o).id (fold o U)) (split o F K))
          ((side P o).comp ((sideM P o).cross (fold o U) (fold o F) (fold o K))
            ((side P o).comp ((sideM P o).tensor ((side P o).id (fold o F)) (join o U K))
              (join o F (U ++ K))))) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  apply side_ext o
  intro A a
  rw [ExchangeScript.component]
  erw [C.assoc (split o U (F ++ K)),
    C.assoc (M.tensor (C.id (fold o U)) (split o F K)),
    C.assoc (M.cross (fold o U) (fold o F) (fold o K)),
    C.assoc (M.tensor (C.id (fold o F)) (join o U K))]
  cases At.cases_append F (U ++ K) a with
  | inl ha =>
    obtain ⟨a,rfl⟩ := ha
    rw [swapBlocks_before,join_before,← C.assoc (M.tensor (C.id (fold o F)) (join o U K)),
      ← D.fst_nat,C.comp_id,← C.assoc (M.cross _ _ _),cross_first,C.assoc,
      ← C.assoc (M.tensor (C.id (fold o U)) (split o F K)),← D.snd_nat,C.assoc,
      split_before,split_shift]
  | inr ha =>
    obtain ⟨a,rfl⟩ := ha
    cases At.cases_append U K a with
    | inl ha =>
      obtain ⟨a,rfl⟩ := ha
      rw [swapBlocks_middle,join_shift,← C.assoc (M.tensor (C.id (fold o F)) (join o U K)),
        ← D.snd_nat,C.assoc,join_before,← C.assoc (D.snd (fold o F) _),
        ← C.assoc (M.cross _ _ _),cross_second,
        ← C.assoc (M.tensor (C.id (fold o U)) (split o F K)),← D.fst_nat,C.comp_id,
        split_before]
    | inr ha =>
      obtain ⟨a,rfl⟩ := ha
      rw [swapBlocks_tail,join_shift,← C.assoc (M.tensor (C.id (fold o F)) (join o U K)),
        ← D.snd_nat,C.assoc,join_shift,← C.assoc (D.snd (fold o F) _),
        ← C.assoc (M.cross _ _ _),cross_tail,C.assoc,
        ← C.assoc (M.tensor (C.id (fold o U)) (split o F K)),← D.snd_nat,C.assoc,
        split_shift,split_shift]

theorem swapBlocks_split (o : Op) (F U K : List (NormalForm P)) :
    (side P o).comp ((swapBlocks F U K).arrow o)
      ((side P o).comp (split o F (U ++ K))
        ((sideM P o).tensor ((side P o).id (fold o F)) (split o U K))) =
      (side P o).comp (split o U (F ++ K))
        ((side P o).comp ((sideM P o).tensor ((side P o).id (fold o U)) (split o F K))
          ((sideM P o).cross (fold o U) (fold o F) (fold o K))) := by
  let C := side P o
  let M := sideM P o
  rw [swapBlocks_arrow]
  erw [C.assoc (split o U (F ++ K)),
    C.assoc (M.tensor (C.id (fold o U)) (split o F K)),
    C.assoc (M.cross (fold o U) (fold o F) (fold o K)),
    C.assoc (M.tensor (C.id (fold o F)) (join o U K))]
  rw [← C.assoc (join o F (U ++ K)),join_split,C.id_comp,
    M.tensor_comp,
    C.id_comp,join_split,M.tensor_id,C.comp_id]

end BinaryMix
end DosenPetric.Reduced.Gentzen
