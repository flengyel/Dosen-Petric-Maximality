module

public import DosenPetric.GentzenBlockedConjunctionRank

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
theorem duplicate_head_assoc (A B : O) :
    C.comp (M.tensor (D.diag A) (C.id B)) (M.assocL A A B) =
      D.pair (D.fst A B) (C.id (M.obj A B)) := by
  apply D.ext
  · simp only [D.assocL_pair hu,D.tensor_pair,D.pair_pre,D.pair_fst,D.pair_snd,
      D.pair_fst_comp,D.diag_fst,C.comp_id,C.assoc]
  · simp only [D.assocL_pair hu,D.tensor_pair,D.pair_pre,D.pair_fst_comp,
      D.pair_snd,D.diag_snd,C.comp_id,C.assoc]
    have he := D.pair_eta (C.id (M.obj A B))
    simpa only [C.id_comp] using he

end DiagonalData
namespace Reduced.Gentzen.SequentialRepair
variable {P : Type u}

def headRoute (I F : List (NormalForm P)) : Route (I++F) (I++(I++F)) :=
  (Route.takeFirst I F).append (Route.identity (I++F))

theorem head_square (o : Op) (I F : List (NormalForm P)) :
    (side P o).comp (join o I F)
      ((side P o).comp ((headRoute I F).sideArrow o)
        ((side P o).comp (split o I (I++F))
          ((sideM P o).tensor ((side P o).id (fold o I)) (split o I F)))) =
      (side P o).comp ((sideM P o).tensor ((sideD P o).diag (fold o I)) ((side P o).id (fold o F)))
        ((sideM P o).assocL (fold o I) (fold o I) (fold o F)) := by
  let S := side P o
  let M := sideM P o
  let D := sideD P o
  have hs := Route.append_split o (Route.takeFirst I F) (Route.identity (I++F))
  rw [Route.identity_arrow] at hs
  change S.comp (join o I F) (S.comp ((headRoute I F).sideArrow o)
    (S.comp (split o I (I++F)) (M.tensor (S.id (fold o I)) (split o I F)))) = _
  rw [← S.assoc ((headRoute I F).sideArrow o)]
  change S.comp (join o I F)
    (S.comp (S.comp (((Route.takeFirst I F).append (Route.identity (I++F))).sideArrow o)
      (split o I (I++F))) _) = _
  rw [hs,D.tensor_pair,D.pair_pre,D.pair_fst_comp,D.pair_snd_comp,S.comp_id,S.id_comp,
    D.pair_pre,join_split]
  have ht : S.comp (join o I F) ((Route.takeFirst I F).sideArrow o) = D.fst (fold o I) (fold o F) := by
    rw [Route.takeFirst_arrow,← S.assoc,join_split,S.id_comp]
  rw [ht]
  exact ((sideD P o).duplicate_head_assoc (side_unit o) (fold o I) (fold o F)).symm

theorem head_decoded (o : Op) (I F : List (NormalForm P)) :
    (side P o).comp ((headRoute I F).sideArrow o)
      ((side P o).comp (split o I (I++F))
        ((sideM P o).tensor ((side P o).id (fold o I)) (split o I F))) =
      (side P o).comp (split o I F)
        ((side P o).comp ((sideM P o).tensor ((sideD P o).diag (fold o I)) ((side P o).id (fold o F)))
          ((sideM P o).assocL (fold o I) (fold o I) (fold o F))) := by
  let S := side P o
  apply DiagonalData.cancel_left (C:=S) _ _ (join o I F) (split o I F) (split_join o I F)
  rw [head_square,← S.assoc (join o I F),join_split,S.id_comp]

def prefixRepair {F D I R : List (NormalForm P)} (g : G P (I++(I++F)) (R++(R++D))) :
    G P (I++F) (R++D) :=
  (headRoute I F).program.left ((headRoute R D).program.right g)

theorem prefixRepair_count {F D I R : List (NormalForm P)} (g : G P (I++(I++F)) (R++(R++D))) :
    (prefixRepair g).cutCount = g.cutCount := by
  rw [prefixRepair,StructuralProgram.left_count,StructuralProgram.right_count]

theorem prefixRepair_congr {F D I R : List (NormalForm P)} (g g' : G P (I++(I++F)) (R++(R++D)))
    (he : ofTerm g.denote = ofTerm g'.denote) : ofTerm (prefixRepair g).denote = ofTerm (prefixRepair g').denote := by
  simp only [prefixRepair,StructuralProgram.left_denote,StructuralProgram.right_denote,he]

end Reduced.Gentzen.SequentialRepair
end DosenPetric
