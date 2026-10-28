module

public import DosenPetric.GentzenPrincipalDisjunctionNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- The reverse list-association comparison, for both context sides. -/
theorem split_assoc_inverse (o : Op) (F U V : List (NormalForm P)) :
    (side P o).comp ((ExchangeScript.appendAssoc F U V).inverse.arrow o)
      ((side P o).comp (split o F (U ++ V))
        ((sideM P o).tensor ((side P o).id (fold o F)) (split o U V))) =
      (side P o).comp (split o (F ++ U) V)
        ((side P o).comp ((sideM P o).tensor (split o F U) ((side P o).id (fold o V)))
          ((sideM P o).assocL (fold o F) (fold o U) (fold o V))) := by
  let C := side P o
  let M := sideM P o
  let p := ExchangeScript.appendAssoc F U V
  apply DiagonalData.cancel_left (C := C) _ _ (p.arrow o) (p.inverse.arrow o) (p.inverse_arrow o)
  rw [← C.assoc, p.arrow_inverse, C.id_comp]
  have he := congrArg (fun k => C.comp k (M.assocL (fold o F) (fold o U) (fold o V)))
    (split_assoc o F U V)
  cases o with
  | conj =>
    dsimp only [C, M, p, side, sideM, category, conjMonoidal] at he ⊢
    simpa only [Laws.assoc, Laws.assocR_L, Laws.comp_id] using he.symm
  | disj =>
    dsimp only [C, M, p, side, sideM, category, opposite, disjMonoidal] at he ⊢
    simpa only [← Laws.assoc, Laws.assocR_L, Laws.id_comp] using he.symm

end DosenPetric.Reduced.Gentzen
