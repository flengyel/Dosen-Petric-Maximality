module

public import DosenPetric.GentzenStructuralLeaves

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem rightOut_assocR (o : Op) (A B : NormalForm P) :
    comp (assocR o A B o.unit) (rightOut o (o.formula A B)) =
      tensor o (id A) (rightOut o B) := by
  rw [← rightOut_tensor, ← Laws.assoc, Laws.assocR_L, Laws.id_comp]

theorem copies_two_product (A : NormalForm P) :
    ofTerm (copies A [[], []] []).product =
      comp (rightOut .conj A) (comp (diag A) (tensor .conj (id A) (rightIn .conj A))) := by
  apply product_positions
  intro B a
  rw [Route.product_get]
  cases a with
  | here =>
    change fst A .top = comp (comp (rightOut .conj A)
      (comp (diag A) (tensor .conj (id A) (rightIn .conj A)))) (fst A (.conj A .top))
    rw [Laws.fst_top]
    simp only [Laws.assoc]
    rw [← Laws.fst_nat, ← Laws.assoc (diag A), Laws.diag_fst, Laws.id_comp, Laws.comp_id]
  | there a => cases a with
    | here =>
      change fst A .top = comp (comp (rightOut .conj A)
        (comp (diag A) (tensor .conj (id A) (rightIn .conj A))))
          (comp (snd A (.conj A .top)) (fst A .top))
      rw [Laws.fst_top]
      simp only [Laws.assoc]
      rw [← Laws.assoc (tensor .conj (id A) (rightIn .conj A)), ← Laws.snd_nat]
      simp only [Laws.assoc]
      rw [Laws.rightIn_Out, Laws.comp_id, Laws.diag_snd, Laws.comp_id]
    | there a => cases a

theorem copies_two_coproduct (A : NormalForm P) :
    ofTerm (copies A [[], []] []).coproduct =
      comp (tensor .disj (id A) (rightOut .disj A)) (comp (codiag A) (rightIn .disj A)) := by
  apply coproduct_positions
  intro B a
  rw [Route.coproduct_get]
  cases a with
  | here =>
    change inl A .bot = comp (inl A (.disj A .bot))
      (comp (tensor .disj (id A) (rightOut .disj A)) (comp (codiag A) (rightIn .disj A)))
    rw [← Laws.assoc, Laws.inl_nat, Laws.id_comp,
      ← Laws.assoc (inl A A), Laws.inl_codiag, Laws.id_comp, Laws.inl_bot]
  | there a => cases a with
    | here =>
      change inl A .bot = comp (comp (inl A .bot) (inr A (.disj A .bot)))
        (comp (tensor .disj (id A) (rightOut .disj A)) (comp (codiag A) (rightIn .disj A)))
      simp only [Laws.assoc]
      rw [← Laws.assoc (inr A (.disj A .bot)), Laws.inr_nat]
      simp only [← Laws.assoc]
      rw [Laws.inl_bot, Laws.rightIn_Out, Laws.id_comp, Laws.inr_codiag, Laws.id_comp]
    | there a => cases a

namespace G

def diagProof (A : NormalForm P) : G P [A] [.conj A A] :=
  .contractL A [[], []] [] [.conj A A] (Nat.le_refl 2) (.conjR (identityNF A) (identityNF A))

def codiagProof (A : NormalForm P) : G P [.disj A A] [A] :=
  .contractR [.disj A A] A [[], []] [] (Nat.le_refl 2) (.disjL (identityNF A) (identityNF A))

theorem diagProof_value (A : NormalForm P) : decode (diagProof A).denote = diag A := by
  change comp (rightIn .conj A)
    (comp (comp (ofTerm (copies A [[], []] []).product)
      (ofTerm (G.conjR (identityNF A) (identityNF A)).denote)) (rightOut .disj (.conj A A))) = _
  rw [Laws.assoc, conjRight_empty, output_out, identityNF_value, Laws.comp_id, copies_two_product]
  simp only [Laws.assoc]
  rw [← Laws.assoc (rightIn .conj A), Laws.rightIn_Out, Laws.id_comp,
    ← rightIn_assocL]
  have hs : comp (comp (rightIn .conj (.conj A A)) (assocL .conj A A .top))
      (ofTerm (append .conj [A] [A]).invTerm) =
        tensor .conj (rightIn .conj A) (rightIn .conj A) := by
    rw [Laws.assoc, single_split]
  rw [← Laws.assoc (comp (rightIn .conj (.conj A A)) (assocL .conj A A .top)), hs]
  rw [Laws.tensor_comp]
  simp only [Laws.rightIn_Out, Laws.tensor_id, Laws.comp_id]

theorem codiagProof_value (A : NormalForm P) : decode (codiagProof A).denote = codiag A := by
  have hleft : ofTerm (G.disjL (identityNF A) (identityNF A)).denote =
      comp (ofTerm (disjInput A A))
        (comp (tensor .disj (ofTerm (identityNF A).denote) (ofTerm (identityNF A).denote))
          (ofTerm (append .disj [A] [A]).toTerm)) := by
    simp only [denote, Rules.disjLeft, disjInput, ofTerm_comp, ofTerm_tensor, Laws.assoc]
    rfl
  change comp (rightIn .conj (.disj A A))
    (comp (comp (ofTerm (G.disjL (identityNF A) (identityNF A)).denote)
      (ofTerm (copies A [[], []] []).coproduct)) (rightOut .disj A)) = _
  rw [hleft, copies_two_coproduct]
  simp only [Laws.assoc]
  rw [← Laws.assoc (rightIn .conj (.disj A A)), disjInput_value,
    ← Laws.assoc (tensor .disj (rightIn .conj A) (rightIn .conj A)),
    Laws.tensor_comp, input_in, identityNF_value, Laws.id_comp, ← rightOut_assocR]
  simp only [Laws.assoc]
  have hj : comp (comp (ofTerm (append .disj [A] [A]).toTerm) (assocR .disj A A .bot))
      (rightOut .disj (.disj A A)) = tensor .disj (rightOut .disj A) (rightOut .disj A) := by
    rw [Laws.assoc, single_join]
  rw [← Laws.assoc (ofTerm (append .disj [A] [A]).toTerm),
    ← Laws.assoc (comp (ofTerm (append .disj [A] [A]).toTerm) (assocR .disj A A .bot)), hj]
  rw [← Laws.assoc (tensor .disj (rightIn .disj A) (rightIn .disj A)), Laws.tensor_comp]
  simp only [Laws.rightIn_Out, Laws.tensor_id, Laws.id_comp, Laws.comp_id]

end G
end DosenPetric.Reduced.Gentzen
