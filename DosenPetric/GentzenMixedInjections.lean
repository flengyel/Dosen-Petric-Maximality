module

public import DosenPetric.GentzenMixedThinning

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- The inner distributive branch in the existing mixedDisj definition. -/
def innerDisj (A X B : NormalForm P) : Hom (.conj (.disj A X) B) (.disj (.conj A B) X) :=
  comp (swap .conj (.disj A X) B)
    (comp (dist B A X) (tensor .disj (swap .conj B A) (id X)))

theorem innerDisj_nat {A X B A' X' B' : NormalForm P}
    (a : Hom A A') (x : Hom X X') (b : Hom B B') :
    comp (innerDisj A X B) (tensor .disj (tensor .conj a b) x) =
      comp (tensor .conj (tensor .disj a x) b) (innerDisj A' X' B') := by
  simp only [innerDisj, Laws.assoc]
  rw [Laws.tensor_comp, Laws.swap_nat, Laws.id_comp]
  have ht : tensor .disj (comp (tensor .conj b a) (swap .conj B' A')) x =
      comp (tensor .disj (tensor .conj b a) x)
        (tensor .disj (swap .conj B' A') (id X')) := by
    rw [Laws.tensor_comp, Laws.comp_id]
  rw [ht]
  rw [← Laws.assoc (dist B A X), Laws.dist_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (swap .conj (.disj A X) B), Laws.swap_nat]
  simp only [Laws.assoc]

theorem mixedDisj_eq (A X B Y : NormalForm P) :
    ofTerm (Term.mixedDisj A X B Y) =
      comp (dist (.disj A X) B Y)
        (comp (tensor .disj (innerDisj A X B) (id Y))
          (assocL .disj (.conj A B) X Y)) := rfl

theorem mixedDisj_nat {A X B Y A' X' B' Y' : NormalForm P}
    (a : Hom A A') (x : Hom X X') (b : Hom B B') (y : Hom Y Y') :
    comp (ofTerm (Term.mixedDisj A X B Y))
      (tensor .disj (tensor .conj a b) (tensor .disj x y)) =
    comp (tensor .conj (tensor .disj a x) (tensor .disj b y))
      (ofTerm (Term.mixedDisj A' X' B' Y')) := by
  simp only [mixedDisj_eq, Laws.assoc]
  rw [Laws.assocL_nat]
  rw [← Laws.assoc (tensor .disj (innerDisj A X B) (id Y)),
    Laws.tensor_comp, Laws.id_comp, innerDisj_nat]
  have ht : tensor .disj
      (comp (tensor .conj (tensor .disj a x) b) (innerDisj A' X' B')) y =
      comp (tensor .disj (tensor .conj (tensor .disj a x) b) y)
        (tensor .disj (innerDisj A' X' B') (id Y')) := by
    rw [Laws.tensor_comp, Laws.comp_id]
  rw [ht]
  simp only [Laws.assoc]
  rw [← Laws.assoc (dist (.disj A X) B Y), Laws.dist_nat]
  simp only [Laws.assoc]

/-- Dropping the second principal factor reduces the inner mixed branch. -/
theorem innerDisj_fst (A X B : NormalForm P) :
    comp (innerDisj A X B) (tensor .disj (fst A B) (id X)) = fst (.disj A X) B := by
  simp only [innerDisj, Laws.assoc]
  rw [Laws.tensor_comp,
    ← Laws.snd_swap, Laws.id_comp, ← Laws.dist_snd]
  exact swap_snd (.disj A X) B

theorem leftOut_assocR (o : Op) (A B : NormalForm P) :
    comp (assocR o o.unit A B) (tensor o (leftOut o A) (id B)) =
      leftOut o (o.formula A B) := by
  have h := shuffle_unit_out o A B
  rw [Laws.tensor_comp, swap_unit_out, Laws.id_comp] at h
  have hh := congrArg (fun k => comp (swap o o.unit (o.formula A B)) k) h
  rw [← Laws.assoc, Laws.swap_swap, Laws.id_comp, swap_unit_out] at hh
  exact hh

theorem mixedDisj_drop (A X B Y : NormalForm P) :
    comp (ofTerm (Term.mixedDisj A X B Y))
      (comp (tensor .disj (fst A B) (id (.disj X Y))) (assocR .disj A X Y)) =
    comp (dist (.disj A X) B Y) (tensor .disj (fst (.disj A X) B) (id Y)) := by
  simp only [mixedDisj_eq, Laws.assoc]
  have ha := Laws.assocL_nat .disj (fst A B) (id X) (id Y)
  rw [Laws.tensor_id] at ha
  rw [← Laws.assoc (assocL .disj (.conj A B) X Y), ha]
  rw [Laws.assoc, Laws.assocL_R, Laws.comp_id]
  rw [Laws.tensor_comp, innerDisj_fst, Laws.id_comp]

theorem bot_pair_fst_diag :
    comp (fst (NormalForm.bot : NormalForm P) .bot) (diag .bot) = id (.conj .bot .bot) := by
  apply conj_ext
  · rw [Laws.assoc, Laws.diag_fst, Laws.comp_id, Laws.id_comp]
  · rw [Laws.assoc, Laws.diag_snd, Laws.comp_id, Laws.id_comp]
    exact toBot_unique _ _

theorem fromBotPair_unique {A : NormalForm P} (f g : Hom (.conj .bot .bot) A) : f = g := by
  apply cancel_left _ _ (diag .bot) (fst .bot .bot) bot_pair_fst_diag
  exact ((disjDiagonal P).toUnit_unique _).trans ((disjDiagonal P).toUnit_unique _).symm

/-- An actual inverse to the injection past the empty principal product. -/
def dropBotPair (W : NormalForm P) : Hom (.disj (.conj .bot .bot) W) W :=
  comp (tensor .disj (fst .bot .bot) (id W)) (leftOut .disj W)

theorem dropBotPair_inr (W : NormalForm P) :
    comp (dropBotPair W) (inr (.conj .bot .bot) W) = id (.disj (.conj .bot .bot) W) := by
  apply disj_ext
  · exact fromBotPair_unique _ _
  · simp only [dropBotPair, ← Laws.assoc]
    rw [Laws.inr_nat, Laws.comp_id]
    have hu : comp (inr (NormalForm.bot : NormalForm P) W) (leftOut .disj W) = id W := by
      have h : inr (NormalForm.bot : NormalForm P) W = leftIn .disj W := (disjDiagonal P).snd_unit W
      rw [h, Laws.leftIn_Out]
    simp only [Laws.id_comp, Laws.assoc]
    rw [← Laws.assoc (inr (NormalForm.bot : NormalForm P) W), hu, Laws.id_comp]

theorem inr_dropBotPair (W : NormalForm P) :
    comp (inr (.conj .bot .bot) W) (dropBotPair W) = id W := by
  simp only [dropBotPair, ← Laws.assoc]
  rw [Laws.inr_nat, Laws.id_comp]
  have hu : inr (NormalForm.bot : NormalForm P) W = leftIn .disj W := (disjDiagonal P).snd_unit W
  rw [hu, Laws.leftIn_Out]

/-- The bottom-principal instance; both auxiliary principal branches are empty. -/
theorem mixedDisj_bot_inr (X Y : NormalForm P) :
    comp (tensor .conj (inr .bot X) (inr .bot Y))
      (ofTerm (Term.mixedDisj .bot X .bot Y)) =
    comp (mix X Y) (inr (.conj .bot .bot) (.disj X Y)) := by
  apply cancel_right _ _ (dropBotPair (.disj X Y)) (inr (.conj .bot .bot) (.disj X Y))
    (dropBotPair_inr (.disj X Y))
  simp only [Laws.assoc]
  rw [inr_dropBotPair, Laws.comp_id]
  rw [dropBotPair, ← leftOut_assocR .disj X Y]
  have hd := congrArg (fun k => comp (tensor .conj (inr .bot X) (inr .bot Y))
      (comp k (tensor .disj (leftOut .disj X) (id Y))))
    (mixedDisj_drop (NormalForm.bot : NormalForm P) X .bot Y)
  calc
    _ = comp (tensor .conj (inr .bot X) (inr .bot Y))
        (comp (dist (.disj .bot X) .bot Y)
          (comp (tensor .disj (fst (.disj .bot X) .bot) (id Y))
            (tensor .disj (leftOut .disj X) (id Y)))) := by
      simpa only [Laws.assoc] using hd
    _ = comp (tensor .conj (inr .bot X) (id Y))
        (comp (mix (.disj .bot X) Y) (tensor .disj (leftOut .disj X) (id Y))) := by
      rw [tensor_separate .conj (inr .bot X) (inr .bot Y)]
      have hm := congrArg (fun k => comp (tensor .conj (inr .bot X) (id Y))
        (comp k (tensor .disj (leftOut .disj X) (id Y))))
        (Laws.dist_mix (.disj .bot X) .bot Y).symm
      simpa only [Laws.assoc] using hm
    _ = mix X Y := by
      rw [Laws.mix_nat, ← Laws.assoc, Laws.tensor_comp, Laws.comp_id]
      have hu : inr (NormalForm.bot : NormalForm P) X = leftIn .disj X := (disjDiagonal P).snd_unit X
      rw [hu, Laws.leftIn_Out, Laws.tensor_id, Laws.id_comp]

/-- The dual mixed injection law needed by right conjunction thinning. -/
theorem mixedDisj_inr (A B X Y : NormalForm P) :
    comp (tensor .conj (inr A X) (inr B Y)) (ofTerm (Term.mixedDisj A X B Y)) =
      comp (mix X Y) (inr (.conj A B) (.disj X Y)) := by
  have ha : inr A X = comp (inr .bot X) (tensor .disj (fromBot A) (id X)) := by
    rw [Laws.inr_nat, Laws.id_comp]
  have hb : inr B Y = comp (inr .bot Y) (tensor .disj (fromBot B) (id Y)) := by
    rw [Laws.inr_nat, Laws.id_comp]
  rw [ha, hb, ← Laws.tensor_comp, Laws.assoc]
  have hn := mixedDisj_nat (fromBot A) (id X) (fromBot B) (id Y)
  rw [Laws.tensor_id] at hn
  rw [← hn, ← Laws.assoc, mixedDisj_bot_inr, Laws.assoc, Laws.inr_nat, Laws.id_comp]

end DosenPetric.Reduced.Gentzen
