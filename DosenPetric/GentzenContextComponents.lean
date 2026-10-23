module

public import DosenPetric.GentzenIsoTransports

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Products for conjunction, and products in the opposite category for disjunction. -/
@[reducible] def side (P : Type u) : Op → Category (NormalForm P)
  | .conj => category P
  | .disj => opposite (category P)

@[reducible] def sideM (P : Type u) (o : Op) : MonoidalData (side P o) where
  obj := o.formula
  unit := o.unit
  tensor := by cases o; exact (conjMonoidal P).tensor; exact (disjMonoidal P).tensor
  tensor_id := by cases o; exact (conjMonoidal P).tensor_id; exact (disjMonoidal P).tensor_id
  tensor_comp := by cases o; exact (conjMonoidal P).tensor_comp; exact (disjMonoidal P).tensor_comp
  assocR := by cases o; exact (conjMonoidal P).assocR; exact (disjMonoidal P).assocR
  assocL := by cases o; exact (conjMonoidal P).assocL; exact (disjMonoidal P).assocL
  assocR_L := by cases o; exact (conjMonoidal P).assocR_L; exact (disjMonoidal P).assocR_L
  assocL_R := by cases o; exact (conjMonoidal P).assocL_R; exact (disjMonoidal P).assocL_R
  assocR_nat := by cases o; exact (conjMonoidal P).assocR_nat; exact (disjMonoidal P).assocR_nat
  assocL_nat := by cases o; exact (conjMonoidal P).assocL_nat; exact (disjMonoidal P).assocL_nat
  swap := by cases o; exact (conjMonoidal P).swap; exact (disjMonoidal P).swap
  swap_nat := by cases o; exact (conjMonoidal P).swap_nat; exact (disjMonoidal P).swap_nat
  rightOut := by cases o; exact (conjMonoidal P).rightOut; exact (disjMonoidal P).rightOut
  rightIn := by cases o; exact (conjMonoidal P).rightIn; exact (disjMonoidal P).rightIn
  leftOut := by cases o; exact (conjMonoidal P).leftOut; exact (disjMonoidal P).leftOut
  leftIn := by cases o; exact (conjMonoidal P).leftIn; exact (disjMonoidal P).leftIn
  rightOut_In := by cases o; exact (conjMonoidal P).rightOut_In; exact (disjMonoidal P).rightOut_In
  rightIn_Out := by cases o; exact (conjMonoidal P).rightIn_Out; exact (disjMonoidal P).rightIn_Out
  leftOut_In := by cases o; exact (conjMonoidal P).leftOut_In; exact (disjMonoidal P).leftOut_In
  leftIn_Out := by cases o; exact (conjMonoidal P).leftIn_Out; exact (disjMonoidal P).leftIn_Out
  rightIn_nat := by cases o; exact (conjMonoidal P).rightIn_nat; exact (disjMonoidal P).rightIn_nat
  leftOut_nat := by cases o; exact (conjMonoidal P).leftOut_nat; exact (disjMonoidal P).leftOut_nat
  triangle := by cases o; exact (conjMonoidal P).triangle; exact (disjMonoidal P).triangle

@[reducible] def sideD (P : Type u) : (o : Op) → DiagonalData (sideM P o)
  | .conj => conjDiagonal P
  | .disj => disjDiagonal P

/-- A selected context component in the appropriate product category. -/
def component (o : Op) {Γ : List (NormalForm P)} {A : NormalForm P} (a : At Γ A) :
    (side P o).Hom (fold o Γ) A :=
  match o with
  | .conj => ofTerm a.projection
  | .disj => ofTerm a.injection

def join (o : Op) (Γ Δ : List (NormalForm P)) :
    (side P o).Hom ((sideM P o).obj (fold o Γ) (fold o Δ)) (fold o (Γ ++ Δ)) :=
  match o with
  | .conj => ofTerm (append .conj Γ Δ).toTerm
  | .disj => ofTerm (append .disj Γ Δ).invTerm

def split (o : Op) (Γ Δ : List (NormalForm P)) :
    (side P o).Hom (fold o (Γ ++ Δ)) ((sideM P o).obj (fold o Γ) (fold o Δ)) :=
  match o with
  | .conj => ofTerm (append .conj Γ Δ).invTerm
  | .disj => ofTerm (append .disj Γ Δ).toTerm

theorem join_split (o : Op) (Γ Δ : List (NormalForm P)) :
    (side P o).comp (join o Γ Δ) (split o Γ Δ) = (side P o).id _ := by
  cases o
  · exact (append .conj Γ Δ).to_inv
  · exact (append .disj Γ Δ).to_inv

theorem split_join (o : Op) (Γ Δ : List (NormalForm P)) :
    (side P o).comp (split o Γ Δ) (join o Γ Δ) = (side P o).id _ := by
  cases o
  · exact (append .conj Γ Δ).inv_to
  · exact (append .disj Γ Δ).inv_to

theorem component_here (o : Op) (A : NormalForm P) (Γ : List (NormalForm P)) :
    component o (.here A Γ) = (sideD P o).fst A (fold o Γ) := by cases o <;> rfl

theorem component_there (o : Op) {Γ : List (NormalForm P)} {A B : NormalForm P} (a : At Γ A) :
    component o (At.there (B := B) a) =
      (side P o).comp ((sideD P o).snd B (fold o Γ)) (component o a) := by cases o <;> rfl

theorem join_nil (o : Op) (Δ : List (NormalForm P)) :
    join o [] Δ = (sideM P o).leftOut (fold o Δ) := by cases o <;> rfl

theorem join_cons (o : Op) (A : NormalForm P) (Γ Δ : List (NormalForm P)) :
    join o (A :: Γ) Δ = (side P o).comp
      ((sideM P o).assocL A (fold o Γ) (fold o Δ))
      ((sideM P o).tensor ((side P o).id A) (join o Γ Δ)) := by cases o <;> rfl

theorem side_unit (o : Op) (A B : NormalForm P) :
    (side P o).comp ((sideM P o).assocR A B (sideM P o).unit)
      ((sideM P o).rightOut ((sideM P o).obj A B)) =
      (sideM P o).tensor ((side P o).id A) ((sideM P o).rightOut B) := by
  cases o
  · exact rightOut_assocR .conj A B
  · exact rightIn_assocL .disj A B

theorem join_before (o : Op) {Γ : List (NormalForm P)} {A : NormalForm P}
    (a : At Γ A) (Δ : List (NormalForm P)) :
    (side P o).comp (join o Γ Δ) (component o (a.before Δ)) =
      (side P o).comp ((sideD P o).fst (fold o Γ) (fold o Δ)) (component o a) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  let q := o
  cases o <;> induction a with
  | here A Γ =>
    simp only [At.before]
    rw [join_cons, component_here, C.assoc, ← D.fst_nat, C.comp_id]
    have h := congrArg (fun k => C.comp (M.assocL A (fold q Γ) (fold q Δ)) k)
      (D.assocR_fst (side_unit q) A (fold q Γ) (fold q Δ))
    rw [← C.assoc, M.assocL_R, C.id_comp] at h
    have h' := congrArg (fun k => C.comp k (D.fst A (fold q Γ))) h
    rw [C.assoc, ← D.fst_nat, C.comp_id] at h'
    exact h'.symm
  | @there A B Γ a ih =>
    simp only [At.before]
    rw [join_cons, component_there, component_there]
    change C.comp (C.comp (M.assocL B (fold q Γ) (fold q Δ))
      (M.tensor (C.id B) (join q Γ Δ)))
      (C.comp (D.snd B (fold q (Γ ++ Δ))) (component q (a.before Δ))) =
      C.comp (D.fst (fold q (B :: Γ)) (fold q Δ))
        (C.comp (D.snd B (fold q Γ)) (component q a))
    rw [C.assoc, ← C.assoc (M.tensor (C.id B) (join q Γ Δ)), ← D.snd_nat, C.assoc, ih]
    have h := D.assocR_fst (side_unit q) B (fold q Γ) (fold q Δ)
    have h' := congrArg (fun k => C.comp (M.assocL B (fold q Γ) (fold q Δ)) k) h
    rw [← C.assoc, M.assocL_R, C.id_comp] at h'
    change C.comp (M.assocL B (fold q Γ) (fold q Δ))
      (C.comp (D.snd B (M.obj (fold q Γ) (fold q Δ)))
        (C.comp (D.fst (fold q Γ) (fold q Δ)) (component q a))) =
      C.comp (D.fst (M.obj B (fold q Γ)) (fold q Δ))
        (C.comp (D.snd B (fold q Γ)) (component q a))
    rw [← C.assoc (D.snd B _), D.snd_nat (C.id B) (D.fst (fold q Γ) (fold q Δ)),
      C.assoc (M.tensor (C.id B) (D.fst (fold q Γ) (fold q Δ))),
      ← C.assoc (M.assocL B (fold q Γ) (fold q Δ)), ← h']

theorem join_shift (o : Op) (Γ : List (NormalForm P)) {Δ : List (NormalForm P)}
    {A : NormalForm P} (a : At Δ A) :
    (side P o).comp (join o Γ Δ) (component o (At.shift Γ a)) =
      (side P o).comp ((sideD P o).snd (fold o Γ) (fold o Δ)) (component o a) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  let q := o
  cases o <;> induction Γ with
  | nil =>
    simp only [At.shift, join_nil]
    exact congrArg (fun k => C.comp k (component q a)) (D.snd_unit (fold q Δ)).symm
  | cons B Γ ih =>
    simp only [At.shift]
    rw [join_cons, component_there]
    change C.comp (C.comp (M.assocL B (fold q Γ) (fold q Δ))
      (M.tensor (C.id B) (join q Γ Δ)))
      (C.comp (D.snd B (fold q (Γ ++ Δ))) (component q (At.shift Γ a))) =
      C.comp (D.snd (fold q (B :: Γ)) (fold q Δ)) (component q a)
    rw [C.assoc, ← C.assoc (M.tensor (C.id B) (join q Γ Δ)), ← D.snd_nat, C.assoc, ih]
    have h := congrArg (fun k => C.comp (M.assocL B (fold q Γ) (fold q Δ)) k)
      (D.assocR_snd B (fold q Γ) (fold q Δ))
    rw [← C.assoc, M.assocL_R, C.id_comp] at h
    have hh := congrArg (fun k => C.comp k (component q a)) h.symm
    change C.comp (M.assocL B (fold q Γ) (fold q Δ))
      (C.comp (D.snd B (M.obj (fold q Γ) (fold q Δ)))
        (C.comp (D.snd (fold q Γ) (fold q Δ)) (component q a))) =
      C.comp (D.snd (M.obj B (fold q Γ)) (fold q Δ)) (component q a)
    have hh' : C.comp (C.comp (M.assocL B (fold q Γ) (fold q Δ))
      (C.comp (D.snd B (M.obj (fold q Γ) (fold q Δ))) (D.snd (fold q Γ) (fold q Δ))))
      (component q a) = C.comp (D.snd (M.obj B (fold q Γ)) (fold q Δ)) (component q a) := hh
    simpa only [C.assoc] using hh'

def exchangeSide (o : Op) (Γ X Y Δ : List (NormalForm P)) :
    (side P o).Hom (fold o (Γ ++ X ++ Y ++ Δ)) (fold o (Γ ++ Y ++ X ++ Δ)) :=
  match o with
  | .conj => ofTerm (exchange .conj Γ X Y Δ).toTerm
  | .disj => ofTerm (exchange .disj Γ X Y Δ).invTerm

theorem exchangeSide_nil (o : Op) (X Y Δ : List (NormalForm P)) :
    exchangeSide o [] X Y Δ = (side P o).comp (split o (X ++ Y) Δ)
      ((side P o).comp
        ((sideM P o).tensor ((side P o).comp (split o X Y)
          ((side P o).comp ((sideM P o).swap (fold o X) (fold o Y)) (join o Y X)))
          ((side P o).id (fold o Δ))) (join o (Y ++ X) Δ)) := by
  cases o <;> simp only [exchangeSide, exchange_nil, exchangeCore, Iso.trans,
    Iso.symm, Iso.tensor, Iso.refl, Iso.swap, join, split, ofTerm_comp, ofTerm_tensor, ofTerm_id]
  · rfl
  · dsimp only [side, sideM, disjMonoidal, opposite, category]
    simp only [Laws.assoc, term_swap]

theorem exchangeSide_cons (o : Op) (A : NormalForm P) (Γ X Y Δ : List (NormalForm P)) :
    exchangeSide o (A :: Γ) X Y Δ =
      (sideM P o).tensor ((side P o).id A) (exchangeSide o Γ X Y Δ) := by
  cases o <;> simp only [exchangeSide, exchange_cons, Iso.tensor, Iso.refl, ofTerm_tensor, ofTerm_id]
  all_goals rfl

def shuffle (o : Op) (X Y : List (NormalForm P)) :
    (side P o).Hom (fold o (X ++ Y)) (fold o (Y ++ X)) :=
  (side P o).comp (split o X Y)
    ((side P o).comp ((sideM P o).swap (fold o X) (fold o Y)) (join o Y X))

theorem shuffle_Y (o : Op) (X : List (NormalForm P)) {Y : List (NormalForm P)}
    {A : NormalForm P} (a : At Y A) :
    (side P o).comp (shuffle o X Y) (component o (a.before X)) =
      component o (At.shift X a) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  apply DiagonalData.cancel_left (C := C) _ _ (join o X Y) (split o X Y) (split_join o X Y)
  unfold shuffle
  rw [← C.assoc, ← C.assoc, join_split, C.id_comp]
  rw [C.assoc, join_before, ← C.assoc, ← D.snd_swap, join_shift]

theorem side_swap_snd (o : Op) (A B : NormalForm P) :
    (side P o).comp ((sideM P o).swap A B) ((sideD P o).snd B A) = (sideD P o).fst A B := by
  cases o
  · exact swap_snd A B
  · exact inr_then_swap B A

theorem shuffle_X (o : Op) {X : List (NormalForm P)} (Y : List (NormalForm P))
    {A : NormalForm P} (a : At X A) :
    (side P o).comp (shuffle o X Y) (component o (At.shift Y a)) =
      component o (a.before Y) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  apply DiagonalData.cancel_left (C := C) _ _ (join o X Y) (split o X Y) (split_join o X Y)
  unfold shuffle
  rw [← C.assoc, ← C.assoc, join_split, C.id_comp]
  rw [C.assoc, join_shift, ← C.assoc, side_swap_snd, join_before]

end DosenPetric.Reduced.Gentzen
