module

public import DosenPetric.ReducedLaws
public import DosenPetric.CartesianFromDiagonal

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}

def conjMonoidal (P : Type u) : MonoidalData (category P) where
  obj := NormalForm.conj
  unit := .top
  tensor := tensor .conj
  tensor_id := Laws.tensor_id .conj
  tensor_comp := Laws.tensor_comp .conj
  assocR := assocR .conj
  assocL := assocL .conj
  assocR_L := Laws.assocR_L .conj
  assocL_R := Laws.assocL_R .conj
  assocR_nat := Laws.assocR_nat .conj
  assocL_nat := Laws.assocL_nat .conj
  swap := swap .conj
  swap_nat := Laws.swap_nat .conj
  rightOut := rightOut .conj
  rightIn := rightIn .conj
  leftOut := leftOut .conj
  leftIn := leftIn .conj
  rightOut_In := Laws.rightOut_In .conj
  rightIn_Out := Laws.rightIn_Out .conj
  leftOut_In := Laws.leftOut_In .conj
  leftIn_Out := Laws.leftIn_Out .conj
  rightIn_nat := Laws.rightIn_nat .conj
  leftOut_nat := Laws.leftOut_nat .conj
  triangle := Laws.triangle .conj

def conjDiagonal (P : Type u) : DiagonalData (conjMonoidal P) where
  diag := diag
  fst := fst
  snd := snd
  diag_nat := Laws.diag_nat
  fst_nat := Laws.fst_nat
  snd_nat := Laws.snd_nat
  diag_fst := Laws.diag_fst
  diag_snd := Laws.diag_snd
  snd_swap := Laws.snd_swap
  fst_unit := Laws.fst_top
  fst_assoc := Laws.fst_assoc
  diag_tensor A B := Laws.diag_tensor A B

theorem inverse_triangle (A B : NormalForm P) :
    assocL .disj A .bot B =
      comp (tensor .disj (rightOut .disj A) (id B)) (tensor .disj (id A) (leftIn .disj B)) := by
  apply DiagonalData.cancel_right (C := category P) _ _
    (assocR .disj A .bot B) (assocL .disj A .bot B) (Laws.assocR_L .disj A .bot B)
  change comp (assocL .disj A .bot B) (assocR .disj A .bot B) =
    comp (comp (tensor .disj (rightOut .disj A) (id B))
      (tensor .disj (id A) (leftIn .disj B))) (assocR .disj A .bot B)
  rw [Laws.assocL_R, Laws.triangle]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .disj (id A) (leftIn .disj B)), Laws.tensor_comp,
    Laws.id_comp, Laws.leftIn_Out, Laws.tensor_id, Laws.id_comp,
    Laws.tensor_comp, Laws.rightOut_In, Laws.comp_id, Laws.tensor_id]

/-- The coproduct laws are the product laws in the opposite category. -/
def disjMonoidal (P : Type u) : MonoidalData (opposite (category P)) where
  obj := NormalForm.disj
  unit := .bot
  tensor := tensor .disj
  tensor_id := Laws.tensor_id .disj
  tensor_comp f g h k := (Laws.tensor_comp .disj h k f g)
  assocR := assocL .disj
  assocL := assocR .disj
  assocR_L := Laws.assocR_L .disj
  assocL_R := Laws.assocL_R .disj
  assocR_nat f g h := (Laws.assocL_nat .disj f g h).symm
  assocL_nat f g h := (Laws.assocR_nat .disj f g h).symm
  swap A B := swap .disj B A
  swap_nat f g := (Laws.swap_nat .disj g f).symm
  rightOut := rightIn .disj
  rightIn := rightOut .disj
  leftOut := leftIn .disj
  leftIn := leftOut .disj
  rightOut_In := Laws.rightOut_In .disj
  rightIn_Out := Laws.rightIn_Out .disj
  leftOut_In := Laws.leftOut_In .disj
  leftIn_Out := Laws.leftIn_Out .disj
  rightIn_nat f := (Laws.rightOut_nat .disj f).symm
  leftOut_nat f := (Laws.leftIn_nat .disj f).symm
  triangle := inverse_triangle

theorem disj_medial (A B C D : NormalForm P) :
    (disjMonoidal P).medial A B C D = medial .disj A C B D := by
  change comp
    (comp (assocL .disj A C (.disj B D))
      (tensor .disj (id A)
        (comp (comp (assocR .disj C B D) (tensor .disj (swap .disj C B) (id D)))
          (assocL .disj B C D))))
    (assocR .disj A B (.disj C D)) = _
  change _ = comp (assocL .disj A C (.disj B D))
    (comp (tensor .disj (id A)
      (comp (assocR .disj C B D)
        (comp (tensor .disj (swap .disj C B) (id D)) (assocL .disj B C D))))
      (assocR .disj A B (.disj C D)))
  rw [Laws.assoc, Laws.assoc]

def disjDiagonal (P : Type u) : DiagonalData (disjMonoidal P) where
  diag := codiag
  fst := inl
  snd := inr
  diag_nat := Laws.codiag_nat
  fst_nat f g := (Laws.inl_nat f g).symm
  snd_nat f g := (Laws.inr_nat f g).symm
  diag_fst := Laws.inl_codiag
  diag_snd := Laws.inr_codiag
  snd_swap := Laws.inr_swap
  fst_unit := Laws.inl_bot
  fst_assoc := Laws.inl_assoc
  diag_tensor A B := by
    change codiag (.disj A B) = comp ((disjMonoidal P).medial A A B B)
      (tensor .disj (codiag A) (codiag B))
    rw [disj_medial]
    exact Laws.codiag_tensor A B


theorem zero_top : zero (NormalForm.top : NormalForm P) = id .top :=
  ((conjDiagonal P).toUnit_unique (zero .top)).trans
    ((conjDiagonal P).toUnit_unique (id .top)).symm

theorem zero_bot : zero (NormalForm.bot : NormalForm P) = id .bot :=
  ((disjDiagonal P).toUnit_unique (zero .bot)).trans
    ((disjDiagonal P).toUnit_unique (id .bot)).symm

theorem fromTop_unique {A : NormalForm P} (f g : Hom .top A) : f = g := by
  have hf := Laws.zero_law f f
  have hg := Laws.zero_law g f
  rw [zero_top, Laws.id_comp] at hf hg
  exact hf.trans hg.symm

theorem toBot_unique {A : NormalForm P} (f g : Hom A .bot) : f = g := by
  have hf := Laws.zero_law f f
  have hg := Laws.zero_law f g
  rw [zero_bot, Laws.comp_id] at hf hg
  exact hf.symm.trans hg

theorem tensor_split (o : Op) {A B C D : NormalForm P}
    (f : Hom B C) (g : Hom C D) :
    tensor o (id A) (comp f g) = comp (tensor o (id A) f) (tensor o (id A) g) := by
  rw [Laws.tensor_comp, Laws.id_comp]

theorem tensor_right_faithful (o : Op) {A B : NormalForm P} (f g : Hom A B)
    (h : tensor o f (id o.unit) = tensor o g (id o.unit)) : f = g := by
  have hh := congrArg (fun k => comp (rightIn o A) (comp k (rightOut o B))) h
  rw [← Laws.rightOut_nat, ← Laws.rightOut_nat, ← Laws.assoc, ← Laws.assoc,
    Laws.rightIn_Out, Laws.id_comp, Laws.id_comp] at hh
  exact hh

theorem cancel_left {A B X : NormalForm P} (f g : Hom A X) (r : Hom B A) (s : Hom A B)
    (hsr : comp s r = id A) (h : comp r f = comp r g) : f = g := by
  have hh := congrArg (fun k => comp s k) h
  rw [← Laws.assoc, ← Laws.assoc, hsr, Laws.id_comp, Laws.id_comp] at hh
  exact hh

/-- The right-unit associativity equation (b delta), derived from pentagon and triangle. -/
theorem rightIn_tensor (o : Op) (A B : NormalForm P) :
    comp (tensor o (id A) (rightIn o B)) (assocR o A B o.unit) =
      rightIn o (o.formula A B) := by
  have h := Laws.pentagon o A B o.unit o.unit
  rw [Laws.triangle o (o.formula A B) o.unit, Laws.triangle o B o.unit,
    tensor_split] at h
  have hn := Laws.assocR_nat o (id A) (id B) (leftOut o o.unit)
  rw [Laws.tensor_id] at hn
  simp only [Laws.assoc] at h
  rw [← Laws.assoc (assocR o A B (o.formula o.unit o.unit)), hn] at h
  have hn' := Laws.assocR_nat o (id A) (rightIn o B) (id o.unit)
  rw [← Laws.assoc (tensor o (id A) (tensor o (rightIn o B) (id o.unit))), ← hn'] at h
  simp only [Laws.assoc] at h
  have h1 := cancel_left _ _
    (tensor o (id A) (tensor o (id B) (leftOut o o.unit)))
    (tensor o (id A) (tensor o (id B) (leftIn o o.unit)))
    (by rw [Laws.tensor_comp, Laws.tensor_comp, Laws.leftIn_Out,
            Laws.id_comp, Laws.id_comp, Laws.tensor_id, Laws.tensor_id]) h
  have h2 := cancel_left _ _
    (assocR o A B o.unit) (assocL o A B o.unit) (Laws.assocL_R o A B o.unit) h1
  rw [Laws.tensor_comp, Laws.id_comp] at h2
  exact (tensor_right_faithful o _ _ h2).symm

theorem rightOut_tensor (o : Op) (A B : NormalForm P) :
    comp (assocL o A B o.unit) (tensor o (id A) (rightOut o B)) =
      rightOut o (o.formula A B) := by
  apply cancel_left _ _ (rightIn o (o.formula A B)) (rightOut o (o.formula A B))
    (Laws.rightOut_In o _)
  rw [← rightIn_tensor o A B, Laws.assoc, ← Laws.assoc (assocR o A B o.unit),
    Laws.assocR_L, Laws.id_comp, Laws.tensor_comp, Laws.rightIn_Out,
    Laws.id_comp, Laws.tensor_id, rightIn_tensor, Laws.rightIn_Out]

theorem swap_unit_out (o : Op) (A : NormalForm P) :
    comp (swap o o.unit A) (rightOut o A) = leftOut o A := by
  cases o with
  | conj =>
    rw [← Laws.fst_top]
    exact (Laws.snd_swap .top A).symm.trans ((conjDiagonal P).snd_unit A)
  | disj =>
    have h : comp (rightIn .disj A) (swap .disj A .bot) = leftIn .disj A :=
      by
        rw [← Laws.inl_bot]
        exact (Laws.inr_swap .bot A).symm.trans ((disjDiagonal P).snd_unit A)
    apply cancel_left _ _ (leftIn .disj A) (leftOut .disj A) (Laws.leftOut_In .disj A)
    rw [← h, Laws.assoc, ← Laws.assoc (swap .disj A .bot), Laws.swap_swap,
      Laws.id_comp, Laws.rightIn_Out]
    rw [h, Laws.leftIn_Out]

theorem shuffle_unit_out (o : Op) (A B : NormalForm P) :
    comp (swap o (o.formula A B) o.unit)
      (comp (assocR o o.unit A B)
        (comp (tensor o (swap o o.unit A) (id B))
          (tensor o (rightOut o A) (id B)))) = rightOut o (o.formula A B) := by
  have h := congrArg (fun k => comp k (rightOut o (o.formula A B)))
    (Laws.hexagon o o.unit A B)
  simp only [Laws.assoc] at h
  have hr : comp (assocR o A B o.unit) (rightOut o (o.formula A B)) =
      tensor o (id A) (rightOut o B) := by
    rw [← rightOut_tensor, ← Laws.assoc, Laws.assocR_L, Laws.id_comp]
  have ht : comp (assocL o A o.unit B) (tensor o (id A) (leftOut o B)) =
      tensor o (rightOut o A) (id B) := by
    apply cancel_left _ _ (assocR o A o.unit B) (assocL o A o.unit B) (Laws.assocL_R o A o.unit B)
    rw [← Laws.assoc, Laws.assocR_L, Laws.id_comp, Laws.triangle,
      Laws.assoc, Laws.tensor_comp, Laws.rightIn_Out, Laws.id_comp, Laws.tensor_id, Laws.comp_id]
  rw [hr, Laws.tensor_comp, Laws.id_comp] at h
  simp only [swap_unit_out] at h
  rw [ht] at h
  have h' := congrArg (fun k => comp (swap o (o.formula A B) o.unit) k) h
  have hs : comp (swap o (o.formula A B) o.unit) (leftOut o (o.formula A B)) =
      rightOut o (o.formula A B) := by
    rw [← swap_unit_out, ← Laws.assoc, Laws.swap_swap, Laws.id_comp]
  rw [hs] at h'
  exact h'.symm

theorem cancel_right {X A B : NormalForm P} (f g : Hom X A) (r : Hom A B) (s : Hom B A)
    (hrs : comp r s = id A) (h : comp f r = comp g r) : f = g := by
  have hh := congrArg (fun k => comp k s) h
  rw [Laws.assoc, Laws.assoc, hrs, Laws.comp_id, Laws.comp_id] at hh
  exact hh

theorem shuffle_unit_in (o : Op) (A B : NormalForm P) :
    comp (tensor o (rightIn o A) (id B))
      (comp (tensor o (swap o A o.unit) (id B))
        (comp (assocL o o.unit A B) (swap o o.unit (o.formula A B)))) =
      rightIn o (o.formula A B) := by
  apply cancel_right _ _ (rightOut o (o.formula A B)) (rightIn o (o.formula A B))
    (Laws.rightOut_In o _)
  rw [← shuffle_unit_out o A B]
  simp only [Laws.assoc]
  rw [← Laws.assoc (swap o o.unit (o.formula A B)), Laws.swap_swap, Laws.id_comp,
    ← Laws.assoc (assocL o o.unit A B), Laws.assocL_R, Laws.id_comp,
    ← Laws.assoc (tensor o (swap o A o.unit) (id B)), Laws.tensor_comp,
    Laws.swap_swap, Laws.id_comp, Laws.tensor_id, Laws.id_comp,
    Laws.tensor_comp, Laws.rightIn_Out, Laws.id_comp, Laws.tensor_id]
  rw [shuffle_unit_out, Laws.rightIn_Out]

/-- (sigma dL), p.270, derived from (d k conjunction) and product units. -/
theorem dist_top (B C : NormalForm P) :
    dist .top B C = comp (leftOut .conj (.disj B C))
      (tensor .disj (leftIn .conj B) (id C)) := by
  have h := Laws.dist_snd (NormalForm.top : NormalForm P) B C
  change snd .top (.disj B C) = comp (dist .top B C) (tensor .disj (snd .top B) (id C)) at h
  have hb : snd (NormalForm.top : NormalForm P) B = leftOut .conj B := (conjDiagonal P).snd_unit B
  have hc : snd (NormalForm.top : NormalForm P) (.disj B C) = leftOut .conj (.disj B C) :=
    (conjDiagonal P).snd_unit _
  rw [hb, hc] at h
  have hh := congrArg (fun k => comp k (tensor .disj (leftIn .conj B) (id C))) h
  rw [Laws.assoc, Laws.tensor_comp, Laws.leftOut_In, Laws.id_comp, Laws.tensor_id, Laws.comp_id] at hh
  exact hh.symm

/-- (delta dL), p.270, derived from (d k disjunction) and coproduct units. -/
theorem dist_bot (A B : NormalForm P) :
    dist A B .bot = comp (tensor .conj (id A) (rightOut .disj B))
      (rightIn .disj (.conj A B)) := by
  have h := Laws.dist_inl A B (NormalForm.bot : NormalForm P)
  rw [Laws.inl_bot, Laws.inl_bot] at h
  have hh := congrArg (fun k => comp (tensor .conj (id A) (rightOut .disj B)) k) h
  rw [← Laws.assoc, Laws.tensor_comp, Laws.rightOut_In, Laws.id_comp, Laws.tensor_id, Laws.id_comp] at hh
  exact hh.symm

theorem swap_unit_in (o : Op) (A : NormalForm P) :
    comp (leftIn o A) (swap o o.unit A) = rightIn o A := by
  apply cancel_right _ _ (rightOut o A) (rightIn o A) (Laws.rightOut_In o A)
  rw [Laws.assoc, swap_unit_out, Laws.leftIn_Out, Laws.rightIn_Out]

theorem distRight_top (A B : NormalForm P) :
    comp (distRight A B .top) (tensor .disj (id A) (rightOut .conj B)) =
      rightOut .conj (.disj A B) := by
  change comp (comp (swap .conj (.disj A B) .top)
    (comp (tensor .conj (id .top) (swap .disj A B))
      (comp (dist .top B A)
        (comp (tensor .disj (swap .conj .top B) (id A)) (swap .disj (.conj B .top) A))))) _ = _
  rw [dist_top]
  simp only [Laws.assoc]
  rw [Laws.swap_nat,
    ← Laws.assoc (tensor .disj (swap .conj .top B) (id A)), Laws.tensor_comp,
    swap_unit_out, Laws.id_comp,
    ← Laws.assoc (tensor .disj (leftIn .conj B) (id A)), Laws.tensor_comp,
    Laws.leftIn_Out, Laws.id_comp, Laws.tensor_id, Laws.id_comp,
    ← Laws.assoc (tensor .conj (id .top) (swap .disj A B)), ← Laws.leftOut_nat,
    Laws.assoc, Laws.swap_swap, Laws.comp_id]
  rw [← swap_unit_out, ← Laws.assoc, Laws.swap_swap, Laws.id_comp]

theorem disj_shuffle_dist_top (A B : NormalForm P) :
    comp (swap .conj (.disj A B) .top)
      (comp (dist .top A B)
        (comp (tensor .disj (swap .conj .top A) (id B))
          (tensor .disj (rightOut .conj A) (id B)))) = rightOut .conj (.disj A B) := by
  rw [dist_top]
  simp only [Laws.assoc]
  rw [Laws.tensor_comp, swap_unit_out, Laws.id_comp,
    Laws.tensor_comp,
    Laws.leftIn_Out, Laws.id_comp, Laws.tensor_id, Laws.comp_id]
  rw [← swap_unit_out, ← Laws.assoc, Laws.swap_swap, Laws.id_comp]

theorem conj_shuffle_dist_bot (A B : NormalForm P) :
    comp (tensor .conj (rightIn .disj A) (id B))
      (comp (tensor .conj (swap .disj A .bot) (id B))
        (comp (distRight .bot A B) (swap .disj .bot (.conj A B)))) =
      rightIn .disj (.conj A B) := by
  change comp (tensor .conj (rightIn .disj A) (id B))
    (comp (tensor .conj (swap .disj A .bot) (id B))
      (comp (comp (swap .conj (.disj .bot A) B)
        (comp (tensor .conj (id B) (swap .disj .bot A))
          (comp (dist B A .bot)
            (comp (tensor .disj (swap .conj B A) (id .bot))
              (swap .disj (.conj A B) .bot))))) _)) = _
  rw [dist_bot]
  simp only [Laws.assoc]
  rw [Laws.swap_swap, Laws.comp_id, Laws.rightIn_nat,
    ← Laws.assoc (tensor .conj (id B) (swap .disj .bot A)),
    Laws.tensor_comp, swap_unit_out, Laws.id_comp,
    ← Laws.assoc (tensor .conj (swap .disj A .bot) (id B)), ← Laws.swap_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (rightIn .disj A) (id B)), ← Laws.swap_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id B) (swap .disj A .bot)), Laws.tensor_comp,
    Laws.id_comp]
  have hs : comp (swap .disj A .bot) (leftOut .disj A) = rightOut .disj A := by
    rw [← swap_unit_out, ← Laws.assoc, Laws.swap_swap, Laws.id_comp]
  rw [hs, ← Laws.assoc (tensor .conj (id B) (rightIn .disj A)), Laws.tensor_comp,
    Laws.id_comp, Laws.rightIn_Out, Laws.tensor_id, Laws.id_comp,
    ← Laws.assoc, Laws.swap_swap, Laws.id_comp]

end DosenPetric.Reduced
