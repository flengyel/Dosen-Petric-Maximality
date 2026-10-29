module

public import DosenPetric.GentzenBlockedLeftDisjRoutes

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.TerminalFold
universe u
variable {P : Type u}

theorem into_cons (C : NormalForm P) (F : List (NormalForm P)) (A : NormalForm P) :
    into (C::F) A =
      comp (assocL .conj C (ante F) A) (tensor .conj (id C) (into F A)) := by
  have hn : comp (tensor .conj (id (.conj C (ante F))) (rightIn .conj A))
      (assocL .conj C (ante F) (.conj A .top)) =
      comp (assocL .conj C (ante F) A)
        (tensor .conj (id C) (tensor .conj (id (ante F)) (rightIn .conj A))) := by
    simpa only [Laws.tensor_id] using
      (Laws.assocL_nat .conj (id C) (id (ante F)) (rightIn .conj A)).symm
  unfold into
  change comp (tensor .conj (id (.conj C (ante F))) (rightIn .conj A))
    (comp (assocL .conj C (ante F) (.conj A .top))
      (tensor .conj (id C) (ofTerm (append .conj F [A]).toTerm))) = _
  rw [← Laws.assoc,hn]
  simp only [Laws.assoc,Laws.tensor_comp,Laws.id_comp]

theorem suffix_into {K U : List (NormalForm P)} (p : StructuralProgram P K U) (A : NormalForm P) :
    comp (into K A) ((p.suffixFixed [A]).arrow .conj) =
      comp (tensor .conj (p.arrow .conj) (id A)) (into U A) := by
  have he := p.suffixFixed_join .conj [A]
  dsimp only [side,sideM,conjMonoidal,category,join] at he
  unfold into
  rw [Laws.assoc]
  erw [he]
  simp only [← Laws.assoc,Laws.tensor_comp,Laws.id_comp,Laws.comp_id]

/-- The exact selected child head commutes with its terminal singleton fold. -/
theorem headBefore_into {U : List (NormalForm P)} {C : NormalForm P} (a : At U C) (A : NormalForm P) :
    comp (assocL .conj C (ante a.erase) A)
      (comp (tensor .conj (id C) (into a.erase A))
        ((LogicalDeletion.headBefore a [A]).arrow .conj)) =
      comp (tensor .conj (a.toHead.arrow .conj) (id A)) (into U A) := by
  rw [← Laws.assoc,← into_cons,BinaryMix.headBefore_structural]
  change comp (into (C::a.erase) A) ((a.toHead.structural.suffixFixed [A]).arrow .conj) = _
  rw [suffix_into,ExchangeScript.structural_arrow]

end DosenPetric.Reduced.Gentzen.TerminalFold
