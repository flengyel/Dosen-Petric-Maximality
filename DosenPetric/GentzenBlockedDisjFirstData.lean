module

public import DosenPetric.GentzenTerminalContractionSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedDisjFirst
universe u
variable {P : Type u}

def block (A B : NormalForm P) (X Y Z : List (NormalForm P)) :
    ContractionBlock P (((X++.disj A B::Y)++Z)++[.disj A B]) (gaps [X,Y++Z]++[.disj A B]) where
  C := .disj A B
  gs := [X,Y++Z]
  tail := []
  upper := by simp only [repeated,List.append_assoc,List.cons_append,List.nil_append]
  lower := rfl

def parametric (A B : NormalForm P) (X Y : List (NormalForm P)) : At (X++.disj A B::Y) (.disj A B) :=
  BlockedMix.firstTag (.disj A B) X Y

theorem first_get (A B : NormalForm P) (X Y Z : List (NormalForm P)) :
    (block A B X Y Z).route.firstBlock.get ((parametric A B X Y).before Z) = (block A B X Y Z).keep := by
  apply At.index_injective
  rw [Route.firstBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,parametric,BlockedMix.firstTag,At.index_before,At.index_shift,At.index,
    Nat.add_zero,gaps,List.append_nil,List.length_append,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem second_get (A B : NormalForm P) (X Y Z : List (NormalForm P)) :
    (block A B X Y Z).route.secondBlock.get (.here (.disj A B) []) = (block A B X Y Z).keep := by
  apply At.index_injective
  rw [Route.secondBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,At.index_shift,At.index,Nat.add_zero,gaps,List.append_nil,List.length_append,
    List.length_nil,List.length_cons,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem first_fixed (A B : NormalForm P) (X Y Z : List (NormalForm P))
    {E : NormalForm P} (v : At ((parametric A B X Y).before Z).erase E) :
    ((block A B X Y Z).route.firstBlock.get (((parametric A B X Y).before Z).retain v)).index ≠
      (block A B X Y Z).keep.index := by
  have hn := ((parametric A B X Y).before Z).retain_ne v
  have hi := (((parametric A B X Y).before Z).retain v).index_lt
  rw [Route.firstBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index,At.index_before]
  have hx : ((parametric A B X Y).before Z).index = X.length := by
    simp only [parametric,BlockedMix.firstTag,At.index_before,At.index_shift,At.index,Nat.add_zero]
  rw [hx] at hn
  simp only [List.length_append,List.length_cons] at hi
  simp only [block,gaps,List.append_nil,List.length_append,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

def rawResidue (A B : NormalForm P) (X Y Z : List (NormalForm P)) :
    Route (block A B X Y Z).keep.erase ((parametric A B X Y).before Z).erase :=
  Route.selectedResidual (block A B X Y Z).route.firstBlock (block A B X Y Z).keep
    ((parametric A B X Y).before Z) (first_fixed A B X Y Z)

def residue (A B : NormalForm P) (X Y Z : List (NormalForm P)) :
    Route (block A B X Y Z).keep.erase ((parametric A B X Y).erase++Z) :=
  (rawResidue A B X Y Z).cast rfl ((parametric A B X Y).erase_before Z)

def parent {A B : NormalForm P} {X Y Z D E : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P (Z++[B]) E) :
    G P (gaps [X,Y++Z]++[.disj A B]) (D++E) :=
  (block A B X Y Z).applyL (Nat.le_refl 2) (D++E) (BlockedSource.disjLLast f g)

theorem parent_source {A B : NormalForm P} {X Y Z D E : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P (Z++[B]) E) :
    parent f g = BlockedSource.left2 (.disj A B) X (Y++Z) [] (D++E)
      ((BlockedSource.disjLLast f g).reindex (by simp only [List.append_assoc,List.cons_append]) rfl) := by
  simp only [parent,block,ContractionBlock.applyL,BlockedSource.left2,G.reindex_trans]
  rfl

end DosenPetric.Reduced.Gentzen.BlockedDisjFirst
