module

public import DosenPetric.GentzenSequentialRepairCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialRepair
universe u
variable {P : Type u}

def headBlock (C : NormalForm P) (F : List (NormalForm P)) :
    ContractionBlock P (C::C::F) (C::F) where
  C := C
  gs := [[],[]]
  tail := F
  upper := rfl
  lower := rfl

theorem headBlock_route (C : NormalForm P) (F : List (NormalForm P)) :
    (headBlock C F).route = .cons (.here C F)
      (.cons (.here C F) ((Route.identity F).map At.there)) := by
  apply Route.ext_get
  intro A a
  apply At.index_injective
  rw [ContractionBlock.get_index]
  cases a with
  | here => rfl
  | there a => cases a with
    | here => rfl
    | there a =>
      simp only [headBlock,copyIndex,Route.get,Route.get_map,Route.get_identity,At.index,
        List.length_nil,Nat.not_lt_zero,ite_false,Nat.zero_add,gaps,List.length_append]
      repeat first | split | omega

theorem headBlock_arrow (C : NormalForm P) (F : List (NormalForm P)) :
    (headBlock C F).route.sideArrow .conj =
      comp (tensor .conj (diag C) (id (ante F))) (assocL .conj C C (ante F)) := by
  rw [headBlock_route]
  change pair (fst C (ante F))
    (pair (fst C (ante F)) (ofTerm ((Route.identity F).map At.there).product)) = _
  have hs : ofTerm ((Route.identity F).map At.there).product = snd C (ante F) := by
    apply product_positions
    intro A a
    rw [Route.product_get,Route.get_map,Route.get_identity]
    rfl
  rw [hs]
  simp only [ProductCalculation.assocL_pair,ProductCalculation.tensor_pair,
    ProductCalculation.pair_pre,ProductCalculation.pair_snd,ProductCalculation.pair_fst_comp,
    Laws.assoc,Laws.diag_fst,Laws.diag_snd,Laws.comp_id]

def headParent {F D : List (NormalForm P)} {C : NormalForm P} (g : G P (C::C::F) D) : G P (C::F) D :=
  (headBlock C F).applyL (Nat.le_refl 2) D g

theorem headParent_denote {F D : List (NormalForm P)} {C : NormalForm P}
    (g : G P (C::C::F) D) :
    ofTerm (headParent g).denote = comp (tensor .conj (diag C) (id (ante F)))
      (comp (assocL .conj C C (ante F)) (ofTerm g.denote)) := by
  rw [headParent,ContractionBlock.denoteL]
  have he := headBlock_arrow C F
  change ofTerm (headBlock C F).route.product = _ at he
  rw [he,Laws.assoc]

def repair {F D I R : List (NormalForm P)} (g : G P ((F++I)++I) ((D++R)++R)) :
    G P (F++I) (D++R) :=
  (tailRoute F I).program.left ((tailRoute D R).program.right g)

theorem repair_count {F D I R : List (NormalForm P)} (g : G P ((F++I)++I) ((D++R)++R)) :
    (repair g).cutCount = g.cutCount := by
  simp only [repair,StructuralProgram.left_count,StructuralProgram.right_count]

theorem repair_congr {F D I R : List (NormalForm P)} (g g' : G P ((F++I)++I) ((D++R)++R))
    (he : ofTerm g.denote = ofTerm g'.denote) : ofTerm (repair g).denote = ofTerm (repair g').denote := by
  simp only [repair,StructuralProgram.left_denote,StructuralProgram.right_denote,he]

end DosenPetric.Reduced.Gentzen.SequentialRepair
