module

public import DosenPetric.GentzenIdentities

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem rightIn_assocL (o : Op) (A B : NormalForm P) :
    comp (rightIn o (o.formula A B)) (assocL o A B o.unit) =
      tensor o (id A) (rightIn o B) := by
  rw [← rightIn_tensor, Laws.assoc, Laws.assocR_L, Laws.comp_id]

theorem inl_assocR (A B C : NormalForm P) :
    comp (inl A (.disj B C)) (assocR .disj A B C) =
      comp (inl A B) (inl (.disj A B) C) := by
  have h := congrArg (fun k => comp (inl A C) k) (Laws.inl_assoc A B C)
  rw [← Laws.assoc, Laws.inl_nat, Laws.assoc,
    Laws.inl_nat, Laws.id_comp] at h
  have hh := congrArg (fun k => comp k (assocR .disj A B C)) h
  simp only [Laws.assoc] at hh
  rw [Laws.assocL_R, Laws.comp_id] at hh
  exact hh.symm

namespace G

def fstProof (A B : NormalForm P) : G P [.conj A B] [A] :=
  .conjL [] [] [A] A B (.thinL [A] [] [A] B (identityNF A))

def sndProof (A B : NormalForm P) : G P [.conj A B] [B] :=
  .conjL [] [] [B] A B (.thinL [] [B] [B] A (identityNF B))

theorem fstProof_value (A B : NormalForm P) : decode (fstProof A B).denote = fst A B := by
  change comp (rightIn .conj (.conj A B))
    (comp (comp (assocL .conj A B .top)
      (comp (ofTerm (Route.thin [A] [] B).product) (ofTerm (identityNF A).denote)))
      (rightOut .disj A)) = _
  simp only [Laws.assoc]
  rw [output_out, identityNF_value, Laws.comp_id]
  have h := Route.product_get (Route.thin [A] [] B) (At.here A [])
  change comp (ofTerm (Route.thin [A] [] B).product) (fst A .top) = fst A (.conj B .top) at h
  rw [Laws.fst_top] at h
  rw [h, ← Laws.assoc, rightIn_assocL, ← Laws.fst_nat, Laws.comp_id]

theorem sndProof_value (A B : NormalForm P) : decode (sndProof A B).denote = snd A B := by
  change comp (rightIn .conj (.conj A B))
    (comp (comp (assocL .conj A B .top)
      (comp (ofTerm (Route.thin [] [B] A).product) (ofTerm (identityNF B).denote)))
      (rightOut .disj B)) = _
  simp only [Laws.assoc]
  rw [output_out, identityNF_value, Laws.comp_id]
  have h := Route.product_get (Route.thin [] [B] A) (At.here B [])
  change comp (ofTerm (Route.thin [] [B] A).product) (fst B .top) =
    comp (snd A (.conj B .top)) (fst B .top) at h
  rw [Laws.fst_top] at h
  rw [h]
  simp only [← Laws.assoc]
  rw [rightIn_assocL, ← Laws.snd_nat, Laws.assoc, Laws.rightIn_Out, Laws.comp_id]

def inlProof (A B : NormalForm P) : G P [A] [.disj A B] :=
  .disjR [A] [] [] A B (.thinR [A] [A] [] B (identityNF A))

def inrProof (A B : NormalForm P) : G P [B] [.disj A B] :=
  .disjR [B] [] [] A B (.thinR [B] [] [B] A (identityNF B))

theorem inlProof_value (A B : NormalForm P) : decode (inlProof A B).denote = inl A B := by
  change comp (rightIn .conj A)
    (comp (comp (comp (ofTerm (identityNF A).denote) (ofTerm (Route.thin [A] [] B).coproduct))
      (assocR .disj A B .bot)) (rightOut .disj (.disj A B))) = _
  simp only [← Laws.assoc]
  rw [input_in, identityNF_value, Laws.id_comp, ← Laws.inl_bot]
  have h := Route.coproduct_get (Route.thin [A] [] B) (At.here A [])
  change comp (inl A .bot) (ofTerm (Route.thin [A] [] B).coproduct) = inl A (.disj B .bot) at h
  rw [h, inl_assocR, Laws.assoc, Laws.inl_bot, Laws.rightIn_Out, Laws.comp_id]

theorem inrProof_value (A B : NormalForm P) : decode (inrProof A B).denote = inr A B := by
  change comp (rightIn .conj B)
    (comp (comp (comp (ofTerm (identityNF B).denote) (ofTerm (Route.thin [] [B] A).coproduct))
      (assocR .disj A B .bot)) (rightOut .disj (.disj A B))) = _
  simp only [← Laws.assoc]
  rw [input_in, identityNF_value, Laws.id_comp, ← Laws.inl_bot]
  have h := Route.coproduct_get (Route.thin [] [B] A) (At.here B [])
  change comp (inl B .bot) (ofTerm (Route.thin [] [B] A).coproduct) =
    comp (inl B .bot) (inr A (.disj B .bot)) at h
  rw [h, Laws.inl_bot, ← Laws.inr_nat (id A) (rightIn .disj B)]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .disj (id A) (rightIn .disj B)), rightIn_tensor,
    Laws.rightIn_Out, Laws.comp_id]

end G
end DosenPetric.Reduced.Gentzen
