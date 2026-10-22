module

public import DosenPetric.ReducedWitnesses

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.Presentation

universe u

variable {P : Type u}

def castHom {A B A' B' : Formula P} (ha : A = A') (hb : B = B') (f : Hom A B) : Hom A' B' :=
  ha ▸ hb ▸ f

theorem castHom_comp {A B C A' B' C' : Formula P}
    (ha : A = A') (hb : B = B') (hc : C = C') (f : Hom A B) (g : Hom B C) :
    castHom ha hc (comp f g) = comp (castHom ha hb f) (castHom hb hc g) := by
  cases ha; cases hb; cases hc; rfl

theorem castHom_tensor (o : Op) {A B C D A' B' C' D' : Formula P}
    (ha : A = A') (hb : B = B') (hc : C = C') (hd : D = D') (f : Hom A C) (g : Hom B D) :
    castHom (congrArgTwo o.formula ha hb) (congrArgTwo o.formula hc hd) (tensor o f g) =
      tensor o (castHom ha hc f) (castHom hb hd g) := by
  cases ha; cases hb; cases hc; cases hd; rfl

namespace NegationNormalization

theorem forward_formula (A : NormalForm P) :
    castHom rfl (congrArg NormalForm.formula (normal_formula A)) (forward A.formula) =
      id A.formula := by
  induction A with
  | lit l => cases l <;> rfl
  | top => rfl
  | bot => rfl
  | conj A B ih ih' =>
    change castHom (congrArgTwo Formula.conj rfl rfl)
      (congrArgTwo Formula.conj (congrArg NormalForm.formula (normal_formula A))
        (congrArg NormalForm.formula (normal_formula B)))
      (tensor .conj (forward A.formula) (forward B.formula)) = _
    rw [castHom_tensor .conj rfl rfl
      (congrArg NormalForm.formula (normal_formula A))
      (congrArg NormalForm.formula (normal_formula B)), ih, ih', Laws.tensor_id]
  | disj A B ih ih' =>
    change castHom (congrArgTwo Formula.disj rfl rfl)
      (congrArgTwo Formula.disj (congrArg NormalForm.formula (normal_formula A))
        (congrArg NormalForm.formula (normal_formula B)))
      (tensor .disj (forward A.formula) (forward B.formula)) = _
    rw [castHom_tensor .disj rfl rfl
      (congrArg NormalForm.formula (normal_formula A))
      (congrArg NormalForm.formula (normal_formula B)), ih, ih', Laws.tensor_id]

theorem backward_formula (A : NormalForm P) :
    castHom (congrArg NormalForm.formula (normal_formula A)) rfl (backward A.formula) =
      id A.formula := by
  induction A with
  | lit l => cases l <;> rfl
  | top => rfl
  | bot => rfl
  | conj A B ih ih' =>
    change castHom
      (congrArgTwo Formula.conj (congrArg NormalForm.formula (normal_formula A))
        (congrArg NormalForm.formula (normal_formula B)))
      (congrArgTwo Formula.conj rfl rfl)
      (tensor .conj (backward A.formula) (backward B.formula)) = _
    rw [castHom_tensor .conj
      (congrArg NormalForm.formula (normal_formula A))
      (congrArg NormalForm.formula (normal_formula B)) rfl rfl, ih, ih', Laws.tensor_id]
  | disj A B ih ih' =>
    change castHom
      (congrArgTwo Formula.disj (congrArg NormalForm.formula (normal_formula A))
        (congrArg NormalForm.formula (normal_formula B)))
      (congrArgTwo Formula.disj rfl rfl)
      (tensor .disj (backward A.formula) (backward B.formula)) = _
    rw [castHom_tensor .disj
      (congrArg NormalForm.formula (normal_formula A))
      (congrArg NormalForm.formula (normal_formula B)) rfl rfl, ih, ih', Laws.tensor_id]

theorem transport_formula (A B : NormalForm P) (f : Hom A.formula B.formula) :
    castHom (congrArg NormalForm.formula (normal_formula A))
      (congrArg NormalForm.formula (normal_formula B)) ((normalization P).transport f) = f := by
  change castHom _ _ (comp (comp (backward A.formula) f) (forward B.formula)) = f
  rw [castHom_comp _ rfl _, castHom_comp _ rfl rfl, backward_formula, forward_formula]
  change comp (comp (id A.formula) f) (id B.formula) = f
  rw [Laws.id_comp, Laws.comp_id]

theorem transport_eq_of_square {A B : Formula P} (f : Hom A B)
    (g : Hom (normal A).formula (normal B).formula)
    (h : comp f (forward B) = comp (forward A) g) :
    (normalization P).transport f = g := by
  change comp (comp (backward A) f) (forward B) = g
  rw [Laws.assoc, h, ← Laws.assoc, backward_forward, Laws.id_comp]

theorem transport_id (A : Formula P) :
    (normalization P).transport (id A) = id (normal A).formula := by
  change comp (comp (backward A) (id A)) (forward A) = _
  rw [Laws.comp_id, backward_forward]

theorem transport_comp {A B C : Formula P} (f : Hom A B) (g : Hom B C) :
    (normalization P).transport (comp f g) =
      comp ((normalization P).transport f) ((normalization P).transport g) := by
  change comp (comp (backward A) (comp f g)) (forward C) =
    comp (comp (comp (backward A) f) (forward B))
      (comp (comp (backward B) g) (forward C))
  simp only [Laws.assoc]
  rw [← Laws.assoc (forward B) (backward B), forward_backward, Laws.id_comp]

theorem transport_tensor_conj {A B C D : Formula P} (f : Hom A C) (g : Hom B D) :
    (normalization P).transport (tensor .conj f g) =
      tensor .conj ((normalization P).transport f) ((normalization P).transport g) := by
  change comp (comp (tensor .conj (backward A) (backward B)) (tensor .conj f g))
      (tensor .conj (forward C) (forward D)) = _
  rw [Laws.tensor_comp, Laws.tensor_comp]
  rfl

theorem transport_tensor_disj {A B C D : Formula P} (f : Hom A C) (g : Hom B D) :
    (normalization P).transport (tensor .disj f g) =
      tensor .disj ((normalization P).transport f) ((normalization P).transport g) := by
  change comp (comp (tensor .disj (backward A) (backward B)) (tensor .disj f g))
      (tensor .disj (forward C) (forward D)) = _
  rw [Laws.tensor_comp, Laws.tensor_comp]
  rfl

end NegationNormalization
end DosenPetric.Presentation
