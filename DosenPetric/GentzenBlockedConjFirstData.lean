module

public import DosenPetric.GentzenSequentialConjFirstSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedConjFirst
universe u
variable {P : Type u}

def block (A B : NormalForm P) (X Y U : List (NormalForm P)) :
    ContractionBlock P (.conj A B::((X++.conj A B::Y)++U))
      (gaps [[],X]++.conj A B::(Y++U)) where
  C := .conj A B
  gs := [[],X]
  tail := Y++U
  upper := by simp only [repeated,List.append_assoc,List.cons_append,List.nil_append]
  lower := rfl

def parametric (A B : NormalForm P) (X Y : List (NormalForm P)) : At (X++.conj A B::Y) (.conj A B) :=
  BlockedMix.firstTag (.conj A B) X Y

theorem fresh_get (A B : NormalForm P) (X Y U : List (NormalForm P)) :
    (block A B X Y U).route.get (.here (.conj A B) ((X++.conj A B::Y)++U)) =
      (block A B X Y U).keep := by
  apply At.index_injective
  rw [ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,At.index,gaps,List.append_nil,List.nil_append,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem parametric_get (A B : NormalForm P) (X Y U : List (NormalForm P)) :
    (block A B X Y U).route.get (.there ((parametric A B X Y).before U)) = (block A B X Y U).keep := by
  apply At.index_injective
  rw [ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,parametric,BlockedMix.firstTag,At.index_before,At.index_shift,At.index,Nat.add_zero,
    gaps,List.append_nil,List.nil_append,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem retained_fixed (A B : NormalForm P) (X Y U : List (NormalForm P))
    {E : NormalForm P} (v : At ((parametric A B X Y).before U).erase E) :
    ((block A B X Y U).route.get (.there (((parametric A B X Y).before U).retain v))).index ≠
      (block A B X Y U).keep.index := by
  have hn := ((parametric A B X Y).before U).retain_ne v
  have hx : ((parametric A B X Y).before U).index = X.length := by
    simp only [parametric,BlockedMix.firstTag,At.index_before,At.index_shift,At.index,Nat.add_zero]
  rw [hx] at hn
  rw [ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,At.index,gaps,List.append_nil,List.nil_append,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

def rawResidue (A B : NormalForm P) (X Y U : List (NormalForm P)) :
    Route (block A B X Y U).keep.erase ((parametric A B X Y).before U).erase :=
  Route.selectedResidual (Route.secondBlock (F:=[.conj A B]) (U:=(X++.conj A B::Y)++U)
    (block A B X Y U).route) (block A B X Y U).keep ((parametric A B X Y).before U)
    (fun v => by simpa only [Route.secondBlock_get,At.shift] using retained_fixed A B X Y U v)

def residue (A B : NormalForm P) (X Y U : List (NormalForm P)) :
    Route (block A B X Y U).keep.erase ((parametric A B X Y).erase++U) :=
  (rawResidue A B X Y U).cast rfl ((parametric A B X Y).erase_before U)

theorem rawResidue_retained (A B : NormalForm P) (X Y U : List (NormalForm P))
    {E : NormalForm P} (v : At ((parametric A B X Y).before U).erase E) :
    (block A B X Y U).route.get (.there (((parametric A B X Y).before U).retain v)) =
      (block A B X Y U).keep.retain ((rawResidue A B X Y U).get v) := by
  have he := Route.selectedResidual_get
    (Route.secondBlock (F:=[.conj A B]) (U:=(X++.conj A B::Y)++U) (block A B X Y U).route)
    (block A B X Y U).keep ((parametric A B X Y).before U)
    (fun v => by simpa only [Route.secondBlock_get,At.shift] using retained_fixed A B X Y U v) v
  simpa only [rawResidue,Route.secondBlock_get,At.shift] using he.symm

def parent {A B : NormalForm P} {Γ Θ X Y U : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::U)) :
    G P (Γ++Θ) (gaps [[],X]++.conj A B::(Y++U)) :=
  (block A B X Y U).applyR (Nat.le_refl 2) _ (G.conjR f g)

theorem parent_source {A B : NormalForm P} {Γ Θ X Y U : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::U)) :
    parent f g = BlockedSource.right2 (.conj A B) (Γ++Θ) [] X (Y++U)
      ((G.conjR f g).reindex rfl (by simp only [List.nil_append,List.append_assoc,List.cons_append])) := by
  simp only [parent,block,ContractionBlock.applyR,BlockedSource.right2,G.reindex_trans]
  rfl

end DosenPetric.Reduced.Gentzen.BlockedConjFirst
