module

public import DosenPetric.GentzenSequentialPrefixRepair

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
theorem duplicate_head_expanded (A B : O) :
    C.comp (M.tensor (D.diag A) (C.id B)) (M.assocL A A B) =
      D.pair (D.fst A B) (D.pair (D.fst A B) (D.snd A B)) := by
  simp only [D.assocL_pair hu,D.tensor_pair,D.pair_pre,D.pair_snd,
    D.pair_fst_comp,D.diag_fst,D.diag_snd,C.comp_id,C.assoc]
end DiagonalData
namespace Reduced.Gentzen.SequentialRepair
variable {P : Type u}

theorem headBlock_side (o : Op) (C : NormalForm P) (F : List (NormalForm P)) :
    (headBlock C F).route.sideArrow o =
      (side P o).comp ((sideM P o).tensor ((sideD P o).diag C) ((side P o).id (fold o F)))
        ((sideM P o).assocL C C (fold o F)) := by
  let S := side P o
  let D := sideD P o
  have he : (headBlock C F).route.sideArrow o = D.pair (D.fst C (fold o F))
      (D.pair (D.fst C (fold o F)) (D.snd C (fold o F))) := by
    apply side_ext o
    intro A a
    rw [Route.sideArrow_get,headBlock_route]
    cases a with
    | here =>
      simp only [Route.get,component_here]
      change D.fst C (fold o F) = S.comp
        (D.pair (D.fst C (fold o F)) (D.pair (D.fst C (fold o F)) (D.snd C (fold o F))))
        (D.fst C (o.formula C (fold o F)))
      exact (D.pair_fst _ _).symm
    | there a => cases a with
      | here =>
        simp only [Route.get,component_here,component_there]
        change D.fst C (fold o F) = S.comp
          (D.pair (D.fst C (fold o F)) (D.pair (D.fst C (fold o F)) (D.snd C (fold o F))))
          (S.comp (D.snd C (o.formula C (fold o F))) (D.fst C (fold o F)))
        rw [← S.assoc,D.pair_snd,D.pair_fst]
      | there a =>
        simp only [Route.get,Route.get_map,Route.get_identity,component_there]
        change S.comp (D.snd C (fold o F)) (component o a) = S.comp
          (D.pair (D.fst C (fold o F)) (D.pair (D.fst C (fold o F)) (D.snd C (fold o F))))
          (S.comp (D.snd C (o.formula C (fold o F)))
            (S.comp (D.snd C (fold o F)) (component o a)))
        rw [← S.assoc,D.pair_snd,← S.assoc,D.pair_snd]
  exact he.trans (D.duplicate_head_expanded (side_unit o) C (fold o F)).symm

theorem headBlock_coproduct (C : NormalForm P) (F : List (NormalForm P)) :
    ofTerm (headBlock C F).route.coproduct =
      comp (assocR .disj C C (succ F)) (tensor .disj (codiag C) (id (succ F))) :=
  headBlock_side .disj C F

def headParentRight {F D : List (NormalForm P)} {C : NormalForm P} (g : G P F (C::C::D)) : G P F (C::D) :=
  (headBlock C D).applyR (Nat.le_refl 2) F g

theorem headParentRight_denote {F D : List (NormalForm P)} {C : NormalForm P}
    (g : G P F (C::C::D)) :
    ofTerm (headParentRight g).denote =
      comp (ofTerm g.denote) (comp (assocR .disj C C (succ D)) (tensor .disj (codiag C) (id (succ D)))) := by
  rw [headParentRight,ContractionBlock.denoteR,headBlock_coproduct]

end Reduced.Gentzen.SequentialRepair
end DosenPetric
