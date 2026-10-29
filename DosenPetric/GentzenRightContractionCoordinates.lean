module

public import DosenPetric.GentzenRightContractionSplice

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric
universe u v
namespace DiagonalData
variable {O : Type u} {C : Category.{u,v} O} {M : MonoidalData C} (D : DiagonalData M)
variable (hu : ∀ A B, C.comp (M.assocR A B M.unit) (M.rightOut (M.obj A B)) =
  M.tensor (C.id A) (M.rightOut B))
variable (hs : ∀ A B, C.comp (M.swap A B) (D.snd B A) = D.fst A B)

include hu hs in
theorem diagonal_double_swap (A Y : O) :
    C.comp (M.tensor (C.id Y) (D.diag A))
      (C.comp (M.assocR Y A A)
        (C.comp (M.tensor (M.swap Y A) (C.id A)) (M.swap (M.obj A Y) A))) =
      C.comp (M.swap Y A) (C.comp (M.tensor (D.diag A) (C.id Y)) (M.assocL A A Y)) := by
  simp only [D.assocR_pair hu,D.assocL_pair hu,D.swap_pair hs,D.tensor_pair,D.pair_pre,
    D.pair_fst,D.pair_snd,D.pair_fst_comp,D.pair_snd_comp,
    C.assoc,D.diag_fst,D.diag_snd,C.comp_id]

end DiagonalData
namespace Reduced.Gentzen.ContractionSplice
variable {P : Type u}

def frontDoubles (C Y : NormalForm P) :
    Hom (.disj C (.disj C Y)) (.disj (.disj Y C) C) :=
  comp (swap .disj C (.disj C Y)) (tensor .disj (swap .disj C Y) (id C))

theorem frontDoubles_merge (C Y : NormalForm P) :
    comp (frontDoubles C Y)
      (comp (assocL .disj Y C C) (tensor .disj (id Y) (codiag C))) =
      comp (assocR .disj C C Y)
        (comp (tensor .disj (codiag C) (id Y)) (swap .disj C Y)) := by
  have he := (disjDiagonal P).diagonal_double_swap (rightIn_assocL .disj) (side_swap_snd .disj) C Y
  dsimp only [disjMonoidal,disjDiagonal,opposite,category] at he
  simpa only [frontDoubles,Laws.assoc] using he

theorem frontDoubles_swap (C Y : NormalForm P) :
    comp (frontDoubles C Y) (swap .disj (.disj Y C) C) =
      tensor .disj (id C) (swap .disj C Y) := by
  rw [frontDoubles,Laws.assoc,← Laws.swap_nat,← Laws.assoc,Laws.swap_swap,Laws.id_comp]

theorem reflected_double_head {R C V Y Z : NormalForm P}
    (h : Hom (.conj C R) Z) (f : Hom V (.disj C (.disj C Y))) :
    PrincipalDisjunction.reflectedSplice (comp (swap .conj R C) h) (comp f (frontDoubles C Y)) =
      comp (splice f h) (tensor .disj (id Z) (swap .disj C Y)) := by
  unfold PrincipalDisjunction.reflectedSplice
  rw [Laws.assoc f,frontDoubles_swap,← Laws.assoc (swap .conj C R),Laws.swap_swap,
    Laws.id_comp,Splice.residual]

end Reduced.Gentzen.ContractionSplice
end DosenPetric
