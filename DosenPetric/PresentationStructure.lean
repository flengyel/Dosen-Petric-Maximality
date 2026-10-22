module

public import DosenPetric.PresentationCategory
public import DosenPetric.CartesianFromDiagonal
public import DosenPetric.Structure

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.Presentation

universe u

variable {P : Type u}

def conjMonoidal (P : Type u) : MonoidalData (category P) where
  obj := Formula.conj
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

theorem inverse_triangle (A B : Formula P) :
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
  obj := Formula.disj
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

theorem disj_medial (A B C D : Formula P) :
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

/-- Binary products/coproducts and terminal/initial objects of the source quotient.
Product eta is derived, not added to the generating equations. -/
def operations (P : Type u) : Structure (category P) where
  fst := fst
  snd := snd
  pair := pair
  pair_fst := (conjDiagonal P).pair_fst
  pair_snd := (conjDiagonal P).pair_snd
  pair_eta := (conjDiagonal P).pair_eta
  inl := inl
  inr := inr
  copair := copair
  inl_copair := (disjDiagonal P).pair_fst
  inr_copair := (disjDiagonal P).pair_snd
  copair_eta := (disjDiagonal P).pair_eta
  toTop := toTop
  toTop_unique := (conjDiagonal P).toUnit_unique
  fromBot := fromBot
  fromBot_unique := (disjDiagonal P).toUnit_unique
  dist := dist

end DosenPetric.Presentation
