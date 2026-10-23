module

public import DosenPetric.GentzenProofInterfaces
public import DosenPetric.GentzenRuleEquations

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem term_dist (A B C : NormalForm P) : ofTerm (.dist A B C) = dist A B C := rfl
theorem term_assocL (o : Op) (A B C : NormalForm P) : ofTerm (.assocL o A B C) = assocL o A B C := rfl
theorem term_swap (o : Op) (A B : NormalForm P) : ofTerm (.swap o A B) = swap o A B := rfl

theorem tensor_factor (o : Op) {A B C D E : NormalForm P}
    (f : Hom A B) (g : Hom C D) (h : Hom D E) :
    tensor o f (comp g h) = comp (tensor o f g) (tensor o (id B) h) := by
  rw [Laws.tensor_comp, Laws.comp_id]

theorem tensor_separate (o : Op) {A B C D : NormalForm P}
    (f : Hom A B) (g : Hom C D) :
    tensor o f g = comp (tensor o f (id C)) (tensor o (id B) g) := by
  rw [Laws.tensor_comp, Laws.comp_id, Laws.id_comp]

/-- Naturality of the actual p.240 conjunction mixed comparison. -/
theorem sourceConj_nat {X Y A B X' Y' A' B' : NormalForm P}
    (x : Hom X X') (y : Hom Y Y') (a : Hom A A') (b : Hom B B') :
    comp (ofTerm (Rules.sourceConj X Y A B))
      (tensor .disj (tensor .conj x a) (tensor .conj y b)) =
    comp (tensor .conj (tensor .conj x y) (tensor .disj a b))
      (ofTerm (Rules.sourceConj X' Y' A' B')) := by
  simp only [Rules.sourceConj, ofTerm_comp, ofTerm_tensor, ofTerm_id, term_dist, term_assocL, term_swap, Laws.assoc]
  rw [Laws.dist_nat]
  rw [← Laws.assoc (tensor .conj (id X) (swap .disj (.conj Y B) A)),
    Laws.tensor_comp, Laws.id_comp, Laws.swap_nat]
  rw [tensor_factor]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id X) (dist Y B A)), Laws.tensor_comp,
    Laws.id_comp, Laws.dist_nat, tensor_factor]
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocL .conj X Y (.disj B A)), Laws.assocL_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id (.conj X Y)) (swap .disj A B)),
    Laws.tensor_comp, Laws.id_comp, Laws.swap_nat, tensor_factor]

  simp only [Laws.assoc]

/-- The right coproduct injection into top or top is an isomorphism. -/
theorem top_inr_codiag :
    comp (codiag (NormalForm.top : NormalForm P)) (inr .top .top) = id (.disj .top .top) := by
  apply disj_ext
  · rw [← Laws.assoc, Laws.inl_codiag, Laws.id_comp, Laws.comp_id]
    exact fromTop_unique _ _
  · rw [← Laws.assoc, Laws.inr_codiag, Laws.id_comp, Laws.comp_id]

theorem inr_then_swap (A B : NormalForm P) : comp (inr A B) (swap .disj A B) = inl B A := by
  rw [Laws.inr_swap, Laws.assoc, Laws.swap_swap, Laws.comp_id]

/-- The right summand specialization of the mixed projection calculation. -/
theorem sourceConj_inr_fst (X Y A B : NormalForm P) :
    comp (tensor .conj (id (.conj X Y)) (inr A B))
      (comp (ofTerm (Rules.sourceConj X Y A B))
        (tensor .disj (fst X A) (fst Y B))) =
    comp (fst (.conj X Y) B) (mix X Y) := by
  simp only [Rules.sourceConj, ofTerm_comp, ofTerm_tensor, ofTerm_id,
    term_dist, term_assocL, term_swap, ← Laws.assoc]
  rw [Laws.tensor_comp, Laws.id_comp, inr_then_swap]
  have ha := Laws.assocL_nat .conj (id X) (id Y) (inl B A)
  rw [Laws.tensor_id] at ha
  rw [← ha]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id X) (tensor .conj (id Y) (inl B A))),
    Laws.tensor_comp, Laws.id_comp, ← Laws.dist_inl]
  rw [← Laws.assoc (tensor .conj (id X) (inl (.conj Y B) A)), Laws.tensor_comp,
    Laws.id_comp, ← Laws.inr_swap]
  rw [tensor_separate .disj (fst X A) (fst Y B)]
  calc
    _ = comp (assocL .conj X Y B)
        (comp (mix X (.conj Y B)) (tensor .disj (id X) (fst Y B))) := by
      simpa only [Laws.assoc] using congrArg
        (fun k => comp (assocL .conj X Y B) (comp k (tensor .disj (id X) (fst Y B))))
        (Laws.dist_mix X A (.conj Y B)).symm
    _ = _ := by
      have he : comp (assocR .conj X Y B) (fst (.conj X Y) B) =
          tensor .conj (id X) (fst Y B) :=
        (conjDiagonal P).assocR_fst (rightOut_assocR .conj) X Y B
      rw [Laws.mix_nat, ← Laws.assoc, ← he,
        ← Laws.assoc, Laws.assocL_R, Laws.id_comp]

/-- The terminal instance, proved by cancellation with an actual isomorphism. -/
theorem sourceConj_top_fst (X Y : NormalForm P) :
    comp (ofTerm (Rules.sourceConj X Y .top .top))
      (tensor .disj (rightOut .conj X) (rightOut .conj Y)) =
    comp (fst (.conj X Y) (.disj .top .top)) (mix X Y) := by
  apply cancel_left _ _
    (tensor .conj (id (.conj X Y)) (inr .top .top))
    (tensor .conj (id (.conj X Y)) (codiag .top))
    (by rw [Laws.tensor_comp, top_inr_codiag, Laws.id_comp, Laws.tensor_id])
  have h := sourceConj_inr_fst X Y .top .top
  rw [Laws.fst_top, Laws.fst_top] at h
  rw [h, ← Laws.assoc, ← Laws.fst_nat, Laws.comp_id]

/-- The required omitted mixed projection law, derived without coherence. -/
theorem sourceConj_fst (X Y A B : NormalForm P) :
    comp (ofTerm (Rules.sourceConj X Y A B))
      (tensor .disj (fst X A) (fst Y B)) =
    comp (fst (.conj X Y) (.disj A B)) (mix X Y) := by
  have hx : fst X A = comp (tensor .conj (id X) (toTop A)) (rightOut .conj X) :=
    (conjDiagonal P).fst_formula X A
  have hy : fst Y B = comp (tensor .conj (id Y) (toTop B)) (rightOut .conj Y) :=
    (conjDiagonal P).fst_formula Y B
  rw [hx, hy]
  rw [← Laws.tensor_comp, ← Laws.assoc]
  rw [sourceConj_nat]
  rw [Laws.tensor_id]
  rw [Laws.assoc, sourceConj_top_fst]
  rw [← Laws.assoc, ← Laws.fst_nat, Laws.comp_id]

end DosenPetric.Reduced.Gentzen
