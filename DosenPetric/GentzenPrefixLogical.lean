module

public import DosenPetric.GentzenPrefixArrows

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ExchangeScript
variable {F U : List (NormalForm P)}

/-- A fixed leading tag is interpreted by tensoring the actual comparison with identity. -/
theorem consFixed_arrow (p : ExchangeScript P F U) (A : NormalForm P) (o : Op) :
    (p.consFixed A).arrow o = (sideM P o).tensor ((side P o).id A) (p.arrow o) := by
  let C := side P o
  let D := sideD P o
  apply side_ext o
  intro E a
  rw [component]
  cases a with
  | here => rw [consFixed_here,component_here,component_here,← D.fst_nat,C.comp_id]
  | there a =>
    rw [consFixed_there,component_there,component_there,← C.assoc,← D.snd_nat,C.assoc,component]

theorem appendAssoc_cons (K F U : List (NormalForm P)) (A : NormalForm P) :
    appendAssoc (A :: K) F U = (appendAssoc K F U).consFixed A := rfl

theorem appendAssoc_inverse_cons (K F U : List (NormalForm P)) (A : NormalForm P) :
    (appendAssoc (A :: K) F U).inverse = (appendAssoc K F U).inverse.consFixed A := rfl

theorem appendAssoc_nil_arrow (F U : List (NormalForm P)) (o : Op) :
    (appendAssoc ([] : List (NormalForm P)) F U).arrow o = (side P o).id (fold o (F ++ U)) := rfl

theorem appendAssoc_nil_inverse_arrow (F U : List (NormalForm P)) (o : Op) :
    (appendAssoc ([] : List (NormalForm P)) F U).inverse.arrow o =
      (side P o).id (fold o (F ++ U)) := rfl

end ExchangeScript

/-- Prefix a logical comparison, retaining the two actual list-association transports. -/
theorem prefixSide_logical (o : Op) (K F U : List (NormalForm P)) (A B : NormalForm P) :
    (side P o).comp ((ExchangeScript.appendAssoc K F (o.formula A B :: U)).arrow o)
      ((side P o).comp (logicalSide o (K ++ F) U A B)
        ((ExchangeScript.appendAssoc K F (A :: B :: U)).inverse.arrow o)) =
      prefixSide o K (logicalSide o F U A B) := by
  let C := side P o
  let M := sideM P o
  induction K with
  | nil =>
    rw [ExchangeScript.appendAssoc_nil_arrow,ExchangeScript.appendAssoc_nil_inverse_arrow]
    change C.comp (C.id _) (C.comp (logicalSide o F U A B) (C.id _)) = logicalSide o F U A B
    rw [C.id_comp,C.comp_id]
  | cons H K ih =>
    rw [ExchangeScript.appendAssoc_cons, ExchangeScript.appendAssoc_inverse_cons,
      ExchangeScript.consFixed_arrow, ExchangeScript.consFixed_arrow]
    change C.comp (M.tensor (C.id H) ((ExchangeScript.appendAssoc K F (o.formula A B :: U)).arrow o))
      (C.comp (logicalSide o (H :: (K ++ F)) U A B)
        (M.tensor (C.id H) ((ExchangeScript.appendAssoc K F (A :: B :: U)).inverse.arrow o))) =
      M.tensor (C.id H) (prefixSide o K (logicalSide o F U A B))
    rw [logicalSide_cons,M.tensor_comp,C.id_comp,M.tensor_comp,C.id_comp,ih]

end DosenPetric.Reduced.Gentzen
