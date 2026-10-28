module

public import DosenPetric.GentzenBinaryMixNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ExchangeScript

def structural : {F U : List (NormalForm P)} → ExchangeScript P F U → StructuralProgram P F U
  | _,_,.identity F => .identity F
  | _,_,.seq p q => .seq p.structural q.structural
  | _,_,.exchange F X Y U => .exchange F X Y U
  | _,_,.reindex hF hU p => .reindex hF hU p.structural

theorem structural_get {F U : List (NormalForm P)} (p : ExchangeScript P F U)
    {E : NormalForm P} (a : At U E) : p.structural.get a = p.get a := by
  induction p with
  | identity => rfl
  | seq p q ih ih' => exact (ih _).trans (congrArg p.get (ih' a))
  | exchange => rfl
  | reindex hF hU p ih => cases hF; cases hU; exact ih a

theorem structural_arrow {F U : List (NormalForm P)} (p : ExchangeScript P F U) (o : Op) :
    p.structural.arrow o = p.arrow o := by
  apply side_ext o
  intro E a
  rw [StructuralProgram.component,component,structural_get]

end ExchangeScript
namespace BinaryMix

/-- Move the selected child tag through an appended fixed mix context. -/
theorem headBefore_structural {F : List (NormalForm P)} {C : NormalForm P}
    (a : At F C) (U : List (NormalForm P)) (o : Op) :
    (LogicalDeletion.headBefore a U).arrow o =
      ((a.toHead.structural.suffixFixed U).reindex rfl rfl).arrow o := by
  apply side_ext o
  intro E b
  rw [ExchangeScript.component,StructuralProgram.component]
  apply congrArg (component o)
  apply At.index_injective
  cases At.cases_append F U b with
  | inl hb =>
    obtain ⟨b,rfl⟩ := hb
    rw [LogicalDeletion.headBefore_index]
    change _ = ((a.toHead.structural.suffixFixed U).get (b.before U)).index
    rw [StructuralProgram.suffixFixed_before,At.index_before,ExchangeScript.structural_get,
      At.index_before,At.toHead_get_index]
  | inr hb =>
    obtain ⟨b,rfl⟩ := hb
    rw [LogicalDeletion.headBefore_tail]
    change _ = ((a.toHead.structural.suffixFixed U).get (At.shift F b)).index
    rw [StructuralProgram.suffixFixed_shift]
    simp only [At.index,At.index_shift,List.length_cons]
    omega

def swapWhole (F U : List (NormalForm P)) : ExchangeScript P (U ++ F) (F ++ U) :=
  (swapBlocks F U []).reindex (by rw [List.append_nil]) (by rw [List.append_nil])

theorem swapWhole_index (F U : List (NormalForm P)) {E : NormalForm P}
    (b : At (F ++ U) E) :
    ((swapWhole F U).get b).index = exchangeIndex 0 F.length U.length b.index := by
  simp only [swapWhole,swapBlocks,ExchangeScript.get,ExchangeScript.rewire,Rewire.get,
    At.index_cast,swapBlocks_index,List.length_nil]

theorem swapWhole_before (F U : List (NormalForm P)) {E : NormalForm P} (b : At F E) :
    (swapWhole F U).get (b.before U) = At.shift U b := by
  apply At.index_injective
  rw [swapWhole_index,At.index_before,At.index_shift]
  have hi := b.index_lt
  unfold exchangeIndex
  split <;> (try split) <;> (try split) <;> omega

theorem swapWhole_shift (F U : List (NormalForm P)) {E : NormalForm P} (b : At U E) :
    (swapWhole F U).get (At.shift F b) = b.before F := by
  apply At.index_injective
  rw [swapWhole_index,At.index_shift,At.index_before]
  have hi := b.index_lt
  unfold exchangeIndex
  split <;> (try split) <;> (try split) <;> omega

theorem swapWhole_join (o : Op) (F U : List (NormalForm P)) :
    (side P o).comp (join o U F) ((swapWhole F U).arrow o) =
      (side P o).comp ((sideM P o).swap (fold o U) (fold o F)) (join o F U) := by
  let S := side P o
  let D := sideD P o
  apply side_ext o
  intro E b
  rw [S.assoc,ExchangeScript.component,S.assoc]
  cases At.cases_append F U b with
  | inl hb =>
    obtain ⟨b,rfl⟩ := hb
    rw [swapWhole_before,join_shift,join_before,← S.assoc,← D.snd_swap]
  | inr hb =>
    obtain ⟨b,rfl⟩ := hb
    rw [swapWhole_shift,join_before,join_shift,← S.assoc,side_swap_snd]

theorem swapWhole_split (o : Op) (F U : List (NormalForm P)) :
    (side P o).comp ((swapWhole F U).arrow o) (split o F U) =
      (side P o).comp (split o U F) ((sideM P o).swap (fold o U) (fold o F)) := by
  let S := side P o
  apply DiagonalData.cancel_left (C := S) _ _ (join o U F) (split o U F) (split_join o U F)
  rw [← S.assoc,swapWhole_join,S.assoc,join_split,S.comp_id,
    ← S.assoc,join_split,S.id_comp]

end BinaryMix
end DosenPetric.Reduced.Gentzen
