module

public import DosenPetric.GentzenLogicalPentagon

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- A logical comparison with a fixed context suffix and explicit list transports. -/
def suffixLogicalSide (o : Op) (F U K : List (NormalForm P)) (A B : NormalForm P) :
    (side P o).Hom (fold o ((F ++ o.formula A B :: U) ++ K))
      (fold o ((F ++ A :: B :: U) ++ K)) :=
  (side P o).comp ((ExchangeScript.appendAssoc F (o.formula A B :: U) K).inverse.arrow o)
    ((side P o).comp (logicalSide o F (U ++ K) A B)
      ((ExchangeScript.appendAssoc F (A :: B :: U) K).arrow o))

theorem suffixLogicalSide_nil (o : Op) (U K : List (NormalForm P)) (A B : NormalForm P) :
    suffixLogicalSide o [] U K A B = logicalSide o [] (U ++ K) A B := by
  rw [suffixLogicalSide,ExchangeScript.appendAssoc_nil_inverse_arrow,
    ExchangeScript.appendAssoc_nil_arrow]
  change (side P o).comp ((side P o).id (fold o (o.formula A B :: (U ++ K))))
    ((side P o).comp (logicalSide o [] (U ++ K) A B)
      ((side P o).id (fold o (A :: B :: (U ++ K))))) = _
  rw [(side P o).id_comp]
  exact (side P o).comp_id (logicalSide o [] (U ++ K) A B)

theorem suffixLogicalSide_cons (o : Op) (H : NormalForm P) (F U K : List (NormalForm P))
    (A B : NormalForm P) : suffixLogicalSide o (H :: F) U K A B =
      (sideM P o).tensor ((side P o).id H) (suffixLogicalSide o F U K A B) := by
  let C := side P o
  let M := sideM P o
  rw [suffixLogicalSide,ExchangeScript.appendAssoc_inverse_cons,ExchangeScript.appendAssoc_cons,
    ExchangeScript.consFixed_arrow,ExchangeScript.consFixed_arrow,logicalSide_cons]
  rw [M.tensor_comp,C.id_comp,M.tensor_comp,C.id_comp]
  rfl

/-- Naturality of the logical comparison through a fixed suffix, including all units. -/
theorem suffixLogicalSide_join (o : Op) (F U K : List (NormalForm P)) (A B : NormalForm P) :
    (side P o).comp (join o (F ++ o.formula A B :: U) K) (suffixLogicalSide o F U K A B) =
      (side P o).comp ((sideM P o).tensor (logicalSide o F U A B) ((side P o).id (fold o K)))
        (join o (F ++ A :: B :: U) K) := by
  let C := side P o
  let M := sideM P o
  induction F with
  | nil =>
    rw [suffixLogicalSide_nil,logicalSide_nil,logicalSide_nil]
    change C.comp (join o (o.formula A B :: U) K) (M.assocL A B (fold o (U ++ K))) =
      C.comp (M.tensor (M.assocL A B (fold o U)) (C.id (fold o K))) (join o (A :: B :: U) K)
    rw [join_cons,join_cons,join_cons]
    change C.comp (C.comp (M.assocL (o.formula A B) (fold o U) (fold o K))
      (M.tensor (C.id (o.formula A B)) (join o U K))) (M.assocL A B (fold o (U ++ K))) =
      C.comp (M.tensor (M.assocL A B (fold o U)) (C.id (fold o K)))
        (C.comp (M.assocL A (o.formula B (fold o U)) (fold o K))
          (M.tensor (C.id A) (C.comp (M.assocL B (fold o U) (fold o K))
            (M.tensor (C.id B) (join o U K)))))
    have hn : C.comp (M.tensor (C.id (o.formula A B)) (join o U K))
        (M.assocL A B (fold o (U ++ K))) =
      C.comp (M.assocL A B (o.formula (fold o U) (fold o K)))
        (M.tensor (C.id A) (M.tensor (C.id B) (join o U K))) := by
      have he := M.assocL_nat (C.id A) (C.id B) (join o U K)
      have hi : M.tensor (C.id A) (C.id B) = C.id (o.formula A B) := M.tensor_id A B
      rw [hi] at he
      exact he.symm
    rw [C.assoc,hn]
    have ht : M.tensor (C.id A) (C.comp (M.assocL B (fold o U) (fold o K))
        (M.tensor (C.id B) (join o U K))) =
      C.comp (M.tensor (C.id A) (M.assocL B (fold o U) (fold o K)))
        (M.tensor (C.id A) (M.tensor (C.id B) (join o U K))) := by
      rw [M.tensor_comp,C.id_comp]
    rw [ht]
    have he := congrArg (fun k => C.comp k
      (M.tensor (C.id A) (M.tensor (C.id B) (join o U K))))
      ((sideD P o).assocL_pentagon (side_unit o) A B (fold o U) (fold o K))
    cases o <;> dsimp only [C,M,side,sideM,category,opposite,conjMonoidal,disjMonoidal] at he ⊢
    all_goals simpa only [Laws.assoc] using he
  | cons H F ih =>
    change C.comp (join o (H :: (F ++ o.formula A B :: U)) K) (suffixLogicalSide o (H :: F) U K A B) =
      C.comp (M.tensor (logicalSide o (H :: F) U A B) (C.id (fold o K)))
        (join o (H :: (F ++ A :: B :: U)) K)
    rw [join_cons,join_cons,suffixLogicalSide_cons,logicalSide_cons]
    change C.comp (C.comp (M.assocL H (fold o (F ++ o.formula A B :: U)) (fold o K))
      (M.tensor (C.id H) (join o (F ++ o.formula A B :: U) K)))
      (M.tensor (C.id H) (suffixLogicalSide o F U K A B)) =
      C.comp (M.tensor (M.tensor (C.id H) (logicalSide o F U A B)) (C.id (fold o K)))
        (C.comp (M.assocL H (fold o (F ++ A :: B :: U)) (fold o K))
          (M.tensor (C.id H) (join o (F ++ A :: B :: U) K)))
    rw [C.assoc,M.tensor_comp,C.id_comp,ih]
    have ht : M.tensor (C.id H) (C.comp
        (M.tensor (logicalSide o F U A B) (C.id (fold o K))) (join o (F ++ A :: B :: U) K)) =
      C.comp (M.tensor (C.id H) (M.tensor (logicalSide o F U A B) (C.id (fold o K))))
        (M.tensor (C.id H) (join o (F ++ A :: B :: U) K)) := by rw [M.tensor_comp,C.id_comp]
    rw [ht,← C.assoc,M.assocL_nat,C.assoc]

theorem suffixLogicalSide_split (o : Op) (F U K : List (NormalForm P)) (A B : NormalForm P) :
    (side P o).comp (suffixLogicalSide o F U K A B) (split o (F ++ A :: B :: U) K) =
      (side P o).comp (split o (F ++ o.formula A B :: U) K)
        ((sideM P o).tensor (logicalSide o F U A B) ((side P o).id (fold o K))) := by
  let C := side P o
  apply DiagonalData.cancel_left (C := C) _ _ (join o (F ++ o.formula A B :: U) K)
    (split o (F ++ o.formula A B :: U) K) (split_join o _ _)
  rw [← C.assoc,suffixLogicalSide_join,C.assoc,join_split,C.comp_id,
    ← C.assoc,join_split,C.id_comp]

end DosenPetric.Reduced.Gentzen
