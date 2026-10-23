module

public import DosenPetric.GentzenStructuralRepresentation

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem single_split_left (o : Op) (A B : NormalForm P) :
    comp (comp (rightIn o (o.formula A B)) (assocL o A B o.unit))
      (ofTerm (append o [A] [B]).invTerm) = tensor o (rightIn o A) (rightIn o B) := by
  rw [Laws.assoc, single_split]

theorem single_join_left (o : Op) (A B : NormalForm P) :
    comp (comp (ofTerm (append o [A] [B]).toTerm) (assocR o A B o.unit))
      (rightOut o (o.formula A B)) = tensor o (rightOut o A) (rightOut o B) := by
  rw [Laws.assoc, single_join]

namespace G

def splitDisj (A B : NormalForm P) : G P [.disj A B] [A, B] := .disjL (identityNF A) (identityNF B)

theorem splitDisj_in (A B : NormalForm P) :
    comp (rightIn .conj (.disj A B)) (ofTerm (splitDisj A B).denote) =
      tensor .disj (id A) (rightIn .disj B) := by
  have hleft : ofTerm (splitDisj A B).denote = comp (ofTerm (disjInput A B))
      (comp (tensor .disj (ofTerm (identityNF A).denote) (ofTerm (identityNF B).denote))
        (ofTerm (append .disj [A] [B]).toTerm)) := by
    simp only [splitDisj, denote, Rules.disjLeft, disjInput, ofTerm_comp, ofTerm_tensor, Laws.assoc]
    rfl
  rw [hleft, ← Laws.assoc, disjInput_value, ← Laws.assoc, Laws.tensor_comp]
  simp only [input_in, identityNF_value, Laws.id_comp]
  exact append_insert .disj A B

theorem collectConj_out (A B : NormalForm P) :
    comp (ofTerm (G.conjR (identityNF A) (identityNF B)).denote) (rightOut .disj (.conj A B)) =
      tensor .conj (id A) (rightOut .conj B) := by
  rw [conjRight_empty]
  simp only [output_out, identityNF_value, Laws.comp_id]
  exact append_remove .conj A B

def mixProof (A B : NormalForm P) : G P [.conj A B] [.disj A B] :=
  .conjL [] [] [.disj A B] A B
    (.disjR [A, B] [] [] A B (.mix (identityNF B) (identityNF A)))

theorem mixProof_value (A B : NormalForm P) : decode (mixProof A B).denote = Reduced.mix A B := by
  change comp (rightIn .conj (.conj A B))
    (comp (comp (assocL .conj A B .top)
      (comp (comp (ofTerm (append .conj [A] [B]).invTerm)
        (comp (tensor .conj (ofTerm (identityNF A).denote) (ofTerm (identityNF B).denote))
          (comp (Reduced.mix (succ [A]) (succ [B])) (ofTerm (append .disj [A] [B]).toTerm))))
        (assocR .disj A B .bot))) (rightOut .disj (.disj A B))) = _
  simp only [← Laws.assoc]
  rw [single_split_left, Laws.tensor_comp]
  simp only [input_in, identityNF_value, Laws.id_comp]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (rightIn .disj A) (rightIn .disj B)), ← Laws.mix_nat,
    single_join, Laws.assoc, Laws.tensor_comp]
  simp only [Laws.rightIn_Out, Laws.tensor_id, Laws.comp_id]

end G

namespace Represented

theorem mix (A B : NormalForm P) : Represented (Reduced.mix A B) := ⟨G.mixProof A B, G.mixProof_value A B⟩

end Represented
end DosenPetric.Reduced.Gentzen
