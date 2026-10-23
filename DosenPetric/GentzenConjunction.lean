module

public import DosenPetric.GentzenUnitLaws

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem conjRight_empty {Γ Θ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ [A]) (g : G P Θ [B]) :
    comp (ofTerm (G.conjR f g).denote) (rightOut .disj (.conj A B)) =
      comp (ofTerm (append .conj Γ Θ).invTerm)
        (tensor .conj (comp (ofTerm f.denote) (rightOut .disj A))
          (comp (ofTerm g.denote) (rightOut .disj B))) := by
  change comp (comp (ofTerm (append .conj Γ Θ).invTerm)
    (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote))
      (comp (ofTerm (Term.mixedDisj A .bot B .bot))
        (tensor .disj (id (.conj A B)) (leftOut .disj .bot))))) _ = _
  simp only [Laws.assoc]
  rw [mixedDisj_bot, Laws.tensor_comp]

/-- All trailing-unit insertions in the singleton multiplicative input. -/
theorem single_split (o : Op) (A B : NormalForm P) :
    comp (rightIn o (o.formula A B))
      (comp (assocL o A B o.unit) (ofTerm (append o [A] [B]).invTerm)) =
      tensor o (rightIn o A) (rightIn o B) := by
  change comp (rightIn o (o.formula A B))
    (comp (assocL o A B o.unit)
      (comp (tensor o (id A) (leftIn o (o.formula B o.unit)))
        (assocR o A o.unit (o.formula B o.unit)))) = _
  rw [← rightIn_tensor o A B]
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocR o A B o.unit), Laws.assocR_L, Laws.id_comp,
    ← Laws.assoc (tensor o (id A) (rightIn o B)), Laws.tensor_comp, Laws.id_comp,
    ← Laws.leftIn_nat]
  rw [tensor_split, Laws.assoc, ← Laws.assocR_nat]
  rw [Laws.triangle]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor o (id A) (leftIn o B)), Laws.tensor_comp,
    Laws.id_comp, Laws.leftIn_Out, Laws.tensor_id, Laws.id_comp,
    Laws.tensor_comp, Laws.tensor_id, Laws.id_comp, Laws.comp_id]

namespace G

def tensorConj {A B C D : NormalForm P} (f : G P [A] [B]) (g : G P [C] [D]) :
    G P [.conj A C] [.conj B D] := .conjL [] [] _ A C (.conjR f g)

theorem tensorConj_value {A B C D : NormalForm P} (f : G P [A] [B]) (g : G P [C] [D]) :
    decode (tensorConj f g).denote = tensor .conj (decode f.denote) (decode g.denote) := by
  change comp (rightIn .conj (.conj A C))
    (comp (comp (assocL .conj A C .top) (ofTerm (G.conjR f g).denote))
      (rightOut .disj (.conj B D))) = _
  rw [Laws.assoc (assocL .conj A C .top), conjRight_empty]
  rw [← Laws.assoc (assocL .conj A C .top), ← Laws.assoc, single_split]
  rw [Laws.tensor_comp]
  rfl

end G
end DosenPetric.Reduced.Gentzen
