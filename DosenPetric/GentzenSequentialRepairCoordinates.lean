module

public import DosenPetric.GentzenFreshUnaryRecursion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric
universe u v
namespace DiagonalData
variable {O : Type u} {C : Category.{u,v} O} {M : MonoidalData C} (D : DiagonalData M)
variable (hu : ∀ A B, C.comp (M.assocR A B M.unit) (M.rightOut (M.obj A B)) =
  M.tensor (C.id A) (M.rightOut B))

include hu in
theorem duplicate_tail_assoc (A B : O) :
    C.comp (M.tensor (C.id A) (D.diag B)) (M.assocR A B B) =
      D.pair (C.id (M.obj A B)) (D.snd A B) := by
  apply D.ext
  · simp only [D.assocR_pair hu,D.tensor_pair,D.pair_pre,
      D.pair_fst,D.pair_snd_comp,D.diag_fst,C.comp_id,C.assoc]
    have he := D.pair_eta (C.id (M.obj A B))
    simpa only [C.id_comp] using he
  · simp only [D.assocR_pair hu,D.tensor_pair,D.pair_pre,
      D.pair_fst,D.pair_snd,D.pair_snd_comp,D.diag_snd,C.comp_id,C.assoc]

end DiagonalData
namespace Reduced.Gentzen.SequentialRepair
variable {P : Type u}

def tailRoute (F I : List (NormalForm P)) : Route (F++I) ((F++I)++I) :=
  (Route.identity (F++I)).append (Route.takeSecond F I)

theorem tail_square (o : Op) (F I : List (NormalForm P)) :
    (side P o).comp (join o F I)
      ((side P o).comp ((tailRoute F I).sideArrow o)
        ((side P o).comp (split o (F++I) I)
          ((sideM P o).tensor (split o F I) ((side P o).id (fold o I))))) =
      (side P o).comp ((sideM P o).tensor ((side P o).id (fold o F)) ((sideD P o).diag (fold o I)))
        ((sideM P o).assocR (fold o F) (fold o I) (fold o I)) := by
  let S := side P o
  let M := sideM P o
  let D := sideD P o
  have hs := Route.append_split o (Route.identity (F++I)) (Route.takeSecond F I)
  rw [Route.identity_arrow] at hs
  change S.comp (join o F I) (S.comp ((tailRoute F I).sideArrow o)
    (S.comp (split o (F++I) I) (M.tensor (split o F I) (S.id (fold o I))))) = _
  rw [← S.assoc ((tailRoute F I).sideArrow o)]
  change S.comp (join o F I)
    (S.comp (S.comp (((Route.identity (F++I)).append (Route.takeSecond F I)).sideArrow o)
      (split o (F++I) I)) _) = _
  rw [hs,D.tensor_pair,D.pair_pre,D.pair_fst_comp,D.pair_snd_comp,S.comp_id,S.id_comp,
    D.pair_pre,join_split]
  have ht : S.comp (join o F I) ((Route.takeSecond F I).sideArrow o) = D.snd (fold o F) (fold o I) := by
    rw [Route.takeSecond_arrow,← S.assoc,join_split,S.id_comp]
  rw [ht]
  exact ((sideD P o).duplicate_tail_assoc (side_unit o) (fold o F) (fold o I)).symm

end Reduced.Gentzen.SequentialRepair
end DosenPetric
