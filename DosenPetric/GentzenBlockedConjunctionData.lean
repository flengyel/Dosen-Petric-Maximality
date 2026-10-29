module

public import DosenPetric.GentzenSequentialRouteRepair

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedConjunction
universe u
variable {P : Type u}

def block (A B : NormalForm P) (X Y : List (NormalForm P)) :
    ContractionBlock P ((X++.conj A B::Y)++[.conj A B]) (gaps [X,Y]++[.conj A B]) where
  C := .conj A B
  gs := [X,Y]
  tail := []
  upper := by simp only [repeated,List.append_assoc,List.cons_append,List.nil_append]
  lower := rfl

def parametric (A B : NormalForm P) (X Y : List (NormalForm P)) : At (X++.conj A B::Y) (.conj A B) :=
  BlockedMix.firstTag (.conj A B) X Y

theorem first_get (A B : NormalForm P) (X Y : List (NormalForm P)) :
    (block A B X Y).route.firstBlock.get (parametric A B X Y) = (block A B X Y).keep := by
  apply At.index_injective
  rw [Route.firstBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,parametric,BlockedMix.firstTag,At.index_before,At.index_shift,At.index,
    Nat.add_zero,gaps,List.append_nil,List.length_append,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem second_get (A B : NormalForm P) (X Y : List (NormalForm P)) :
    (block A B X Y).route.secondBlock.get (.here (.conj A B) []) = (block A B X Y).keep := by
  apply At.index_injective
  rw [Route.secondBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,At.index_shift,At.index,Nat.add_zero,gaps,List.append_nil,List.length_append,
    List.length_nil,List.length_cons,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem first_fixed (A B : NormalForm P) (X Y : List (NormalForm P))
    {E : NormalForm P} (v : At (parametric A B X Y).erase E) :
    ((block A B X Y).route.firstBlock.get ((parametric A B X Y).retain v)).index ≠
      (block A B X Y).keep.index := by
  have hn := (parametric A B X Y).retain_ne v
  have hi := ((parametric A B X Y).retain v).index_lt
  rw [Route.firstBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index,At.index_before]
  have hx : (parametric A B X Y).index = X.length := by
    simp only [parametric,BlockedMix.firstTag,At.index_shift,At.index,Nat.add_zero]
  rw [hx] at hn
  simp only [List.length_append,List.length_cons] at hi
  simp only [block,gaps,List.append_nil,List.length_append,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

def residue (A B : NormalForm P) (X Y : List (NormalForm P)) :
    Route (block A B X Y).keep.erase (parametric A B X Y).erase :=
  Route.selectedResidual (block A B X Y).route.firstBlock (block A B X Y).keep
    (parametric A B X Y) (first_fixed A B X Y)

def parent {A B : NormalForm P} {X Y D : List (NormalForm P)}
    (f : G P ((X++.conj A B::Y)++[A,B]) D) : G P (gaps [X,Y]++[.conj A B]) D :=
  (block A B X Y).applyL (Nat.le_refl 2) D (BlockedSource.conjLLast _ D A B f)

theorem parent_source {A B : NormalForm P} {X Y D : List (NormalForm P)}
    (f : G P ((X++.conj A B::Y)++[A,B]) D) :
    parent f = BlockedSource.left2 (.conj A B) X Y [] D
      ((BlockedSource.conjLLast (X++.conj A B::Y) D A B f).reindex
        (by simp only [List.append_assoc,List.cons_append]) rfl) := by
  simp only [parent,block,ContractionBlock.applyL,BlockedSource.left2,G.reindex_trans]
  rfl

end DosenPetric.Reduced.Gentzen.BlockedConjunction
