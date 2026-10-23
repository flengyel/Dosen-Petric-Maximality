module

public import DosenPetric.GentzenLogicalPositions

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace Iso

theorem symm_cast {A B A' B' : NormalForm P} (hA : A = A') (hB : B = B') (i : Iso A B) :
    (i.cast hA hB).symm = i.symm.cast hB hA := by cases hA; cases hB; rfl

end Iso

theorem under_symm (o : Op) (Γ : List (NormalForm P)) {A B : NormalForm P} (i : Iso A B) :
    under o Γ i.symm = (under o Γ i).symm := by
  induction Γ with
  | nil => rfl
  | cons C Γ ih => simp only [under,ih]; rfl

/-- Derived comparison packaging the existing two unary logical arrows. -/
def logicalCompare (o : Op) (Γ Θ : List (NormalForm P)) (A B : NormalForm P) :
    Iso (fold o (Γ ++ o.formula A B :: Θ)) (fold o (Γ ++ A :: B :: Θ)) :=
  (under o Γ (Iso.assoc o A B (fold o Θ))).cast
    (prefix_fold o Γ (o.formula A B :: Θ)).symm (prefix_fold o Γ (A :: B :: Θ)).symm

theorem conjLeft_compare (Γ Θ : List (NormalForm P)) (A B : NormalForm P) :
    Rules.conjLeft Γ Θ A B = logicalCompare .conj Γ Θ A B := by
  unfold Rules.conjLeft logicalCompare
  apply eq_of_heq
  change (cast _ (cast _ (under .conj Γ (Iso.assoc .conj A B (ante Θ))))) ≍ _
  exact ((cast_heq _ _).trans (cast_heq _ _)).trans (Iso.cast_heq ..).symm

theorem disjRight_compare (Γ Θ : List (NormalForm P)) (A B : NormalForm P) :
    Rules.disjRight Γ Θ A B = (logicalCompare .disj Γ Θ A B).symm := by
  unfold logicalCompare
  rw [Iso.symm_cast]
  unfold Rules.disjRight
  apply eq_of_heq
  change (cast _ (cast _ (under .disj Γ (Iso.assoc .disj A B (succ Θ)).symm))) ≍ _
  exact ((cast_heq _ _).trans (cast_heq _ _)).trans
    ((heq_of_eq (under_symm .disj Γ (Iso.assoc .disj A B (succ Θ)))).trans (Iso.cast_heq ..).symm)

theorem logicalCompare_nil (o : Op) (Θ : List (NormalForm P)) (A B : NormalForm P) :
    logicalCompare o [] Θ A B = Iso.assoc o A B (fold o Θ) := rfl

theorem logicalCompare_cons (o : Op) (H : NormalForm P) (Γ Θ : List (NormalForm P)) (A B : NormalForm P) :
    logicalCompare o (H :: Γ) Θ A B = Iso.tensor o (Iso.refl H) (logicalCompare o Γ Θ A B) :=
  Iso.cast_tensor o H (prefix_fold o Γ (o.formula A B :: Θ)).symm
    (prefix_fold o Γ (A :: B :: Θ)).symm (under o Γ (Iso.assoc o A B (fold o Θ)))

def logicalSide (o : Op) (Γ Θ : List (NormalForm P)) (A B : NormalForm P) :
    (side P o).Hom (fold o (Γ ++ o.formula A B :: Θ)) (fold o (Γ ++ A :: B :: Θ)) :=
  match o with
  | .conj => ofTerm (logicalCompare .conj Γ Θ A B).toTerm
  | .disj => ofTerm (logicalCompare .disj Γ Θ A B).invTerm

theorem logicalSide_nil (o : Op) (Θ : List (NormalForm P)) (A B : NormalForm P) :
    logicalSide o [] Θ A B = (sideM P o).assocL A B (fold o Θ) := by cases o <;> rfl

theorem logicalSide_cons (o : Op) (H : NormalForm P) (Γ Θ : List (NormalForm P)) (A B : NormalForm P) :
    logicalSide o (H :: Γ) Θ A B = (sideM P o).tensor ((side P o).id H) (logicalSide o Γ Θ A B) := by
  cases o <;> simp only [logicalSide,logicalCompare_cons,Iso.tensor,Iso.refl,ofTerm_tensor,ofTerm_id] <;> rfl

theorem logical_head_first (o : Op) (A B X : NormalForm P) :
    (side P o).comp ((sideM P o).assocL A B X) ((sideD P o).fst A (o.formula B X)) =
      (side P o).comp ((sideD P o).fst (o.formula A B) X) ((sideD P o).fst A B) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  apply DiagonalData.cancel_left (C := C) _ _ (M.assocR A B X) (M.assocL A B X) (M.assocL_R A B X)
  rw [← C.assoc,M.assocR_L,C.id_comp,← C.assoc,D.assocR_fst (side_unit o),← D.fst_nat,C.comp_id]

theorem logical_head_second (o : Op) (A B X : NormalForm P) :
    (side P o).comp ((sideM P o).assocL A B X)
      ((side P o).comp ((sideD P o).snd A (o.formula B X)) ((sideD P o).fst B X)) =
      (side P o).comp ((sideD P o).fst (o.formula A B) X) ((sideD P o).snd A B) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  apply DiagonalData.cancel_left (C := C) _ _ (M.assocR A B X) (M.assocL A B X) (M.assocL_R A B X)
  rw [← C.assoc,M.assocR_L,C.id_comp,← C.assoc,D.assocR_fst (side_unit o),← D.snd_nat]

theorem logical_head_tail (o : Op) (A B X : NormalForm P) :
    (side P o).comp ((sideM P o).assocL A B X)
      ((side P o).comp ((sideD P o).snd A (o.formula B X)) ((sideD P o).snd B X)) =
      (sideD P o).snd (o.formula A B) X := by
  have h := congrArg (fun k => (side P o).comp ((sideM P o).assocL A B X) k)
    ((sideD P o).assocR_snd A B X)
  rw [← (side P o).assoc,(sideM P o).assocL_R,(side P o).id_comp] at h
  exact h.symm

theorem logical_prefix (o : Op) {Γ : List (NormalForm P)} (Θ : List (NormalForm P))
    (A B : NormalForm P) {E : NormalForm P} (a : At Γ E) :
    (side P o).comp (logicalSide o Γ Θ A B) (component o (a.before (A :: B :: Θ))) =
      component o (a.before (o.formula A B :: Θ)) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  let q := o
  cases o <;> induction a with
  | here H Γ =>
    simp only [At.before,logicalSide_cons,component_here]
    rw [← D.fst_nat,C.comp_id]
  | @there E H Γ a ih =>
    simp only [At.before,logicalSide_cons,component_there]
    change C.comp (M.tensor (C.id H) (logicalSide q Γ Θ A B))
      (C.comp (D.snd H (fold q (Γ ++ A :: B :: Θ))) (component q (a.before (A :: B :: Θ)))) =
      C.comp (D.snd H (fold q (Γ ++ q.formula A B :: Θ))) (component q (a.before (q.formula A B :: Θ)))
    rw [← C.assoc,← D.snd_nat,C.assoc,ih]

theorem logical_first (o : Op) (Γ Θ : List (NormalForm P)) (A B : NormalForm P) :
    (side P o).comp (logicalSide o Γ Θ A B)
      (component o (At.shift Γ (.here A (B :: Θ)))) =
    (side P o).comp (component o (At.shift Γ (.here (o.formula A B) Θ))) ((sideD P o).fst A B) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  let q := o
  cases o <;> induction Γ with
  | nil => simpa only [At.shift,logicalSide_nil,component_here] using logical_head_first q A B (fold q Θ)
  | cons H Γ ih =>
    simp only [At.shift,logicalSide_cons,component_there]
    change C.comp (M.tensor (C.id H) (logicalSide q Γ Θ A B))
      (C.comp (D.snd H (fold q (Γ ++ A :: B :: Θ))) (component q (At.shift Γ (.here A (B :: Θ))))) =
      C.comp (C.comp (D.snd H (fold q (Γ ++ q.formula A B :: Θ)))
        (component q (At.shift Γ (.here (q.formula A B) Θ)))) (D.fst A B)
    rw [← C.assoc,← D.snd_nat,C.assoc,ih,← C.assoc]

theorem logical_second (o : Op) (Γ Θ : List (NormalForm P)) (A B : NormalForm P) :
    (side P o).comp (logicalSide o Γ Θ A B)
      (component o (At.shift Γ (.there (.here B Θ)))) =
    (side P o).comp (component o (At.shift Γ (.here (o.formula A B) Θ))) ((sideD P o).snd A B) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  let q := o
  cases o <;> induction Γ with
  | nil => simpa only [At.shift,logicalSide_nil,component_there,component_here] using logical_head_second q A B (fold q Θ)
  | cons H Γ ih =>
    simp only [At.shift,logicalSide_cons,component_there]
    change C.comp (M.tensor (C.id H) (logicalSide q Γ Θ A B))
      (C.comp (D.snd H (fold q (Γ ++ A :: B :: Θ))) (component q (At.shift Γ (.there (.here B Θ))))) =
      C.comp (C.comp (D.snd H (fold q (Γ ++ q.formula A B :: Θ)))
        (component q (At.shift Γ (.here (q.formula A B) Θ)))) (D.snd A B)
    rw [← C.assoc,← D.snd_nat,C.assoc,ih,← C.assoc]

theorem logical_tail (o : Op) (Γ : List (NormalForm P)) (Θ : List (NormalForm P)) (A B : NormalForm P)
    {E : NormalForm P} (a : At Θ E) :
    (side P o).comp (logicalSide o Γ Θ A B) (component o (At.shift Γ (At.shift [A,B] a))) =
      component o (At.shift Γ (At.shift [o.formula A B] a)) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  let q := o
  cases o <;> induction Γ with
  | nil =>
    simp only [At.shift,logicalSide_nil,component_there]
    change C.comp (M.assocL A B (fold q Θ))
      (C.comp (D.snd A (q.formula B (fold q Θ))) (C.comp (D.snd B (fold q Θ)) (component q a))) =
      C.comp (D.snd (q.formula A B) (fold q Θ)) (component q a)
    rw [← C.assoc (D.snd A _),← C.assoc,logical_head_tail]
  | cons H Γ ih =>
    simp only [At.shift,logicalSide_cons,component_there]
    change C.comp (M.tensor (C.id H) (logicalSide q Γ Θ A B))
      (C.comp (D.snd H (fold q (Γ ++ A :: B :: Θ))) (component q (At.shift Γ (At.shift [A,B] a)))) =
      C.comp (D.snd H (fold q (Γ ++ q.formula A B :: Θ))) (component q (At.shift Γ (At.shift [q.formula A B] a)))
    rw [← C.assoc,← D.snd_nat,C.assoc,ih]

theorem logical_survives (o : Op) (Γ Θ : List (NormalForm P)) (A B : NormalForm P)
    {E : NormalForm P} (a : At (Γ ++ A :: B :: Θ) E) (b : At (Γ ++ o.formula A B :: Θ) E)
    (h : At.fixed Γ [A,B] [o.formula A B] Θ a = some b) :
    (side P o).comp (logicalSide o Γ Θ A B) (component o a) = component o b := by
  cases At.cases_append Γ ([A,B] ++ Θ) a with
  | inl ha =>
    obtain ⟨a,rfl⟩ := ha
    rw [At.fixed_before] at h
    cases Option.some.inj h
    exact logical_prefix o Θ A B a
  | inr ha =>
    obtain ⟨a,rfl⟩ := ha
    cases At.cases_append [A,B] Θ a with
    | inl ha => obtain ⟨a,rfl⟩ := ha; rw [At.fixed_middle] at h; cases h
    | inr ha =>
      obtain ⟨a,rfl⟩ := ha
      rw [At.fixed_tail] at h
      cases Option.some.inj h
      exact logical_tail o Γ Θ A B a

end DosenPetric.Reduced.Gentzen
