module

public import DosenPetric.GentzenSequentialDisjBothSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedDisjBoth
universe u
variable {P : Type u}

def block (A B : NormalForm P) (X Y Z T : List (NormalForm P)) :
    ContractionBlock P (((X++.disj A B::Y)++(Z++.disj A B::T))++[.disj A B])
      (gaps [X,Y++Z,T]++[.disj A B]) where
  C := .disj A B
  gs := [X,Y++Z,T]
  tail := []
  upper := by simp only [repeated,List.append_assoc,List.cons_append,List.nil_append]
  lower := rfl

theorem first_get (A B : NormalForm P) (X Y Z T : List (NormalForm P)) :
    (block A B X Y Z T).route.firstBlock.firstBlock.get (BlockedMix.firstTag (.disj A B) X Y) =
      (block A B X Y Z T).keep := by
  apply At.index_injective
  rw [Route.firstBlock_get,Route.firstBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,BlockedMix.firstTag,At.index_before,At.index_shift,At.index,Nat.add_zero,
    gaps,List.append_nil,List.length_append,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem second_get (A B : NormalForm P) (X Y Z T : List (NormalForm P)) :
    (block A B X Y Z T).route.firstBlock.secondBlock.get (BlockedMix.firstTag (.disj A B) Z T) =
      (block A B X Y Z T).keep := by
  apply At.index_injective
  rw [Route.secondBlock_get,Route.firstBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,BlockedMix.firstTag,At.index_before,At.index_shift,At.index,Nat.add_zero,
    gaps,List.append_nil,List.length_append,List.length_cons,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem fresh_get (A B : NormalForm P) (X Y Z T : List (NormalForm P)) :
    (block A B X Y Z T).route.secondBlock.get (.here (.disj A B) []) = (block A B X Y Z T).keep := by
  apply At.index_injective
  rw [Route.secondBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,At.index_shift,At.index,Nat.add_zero,gaps,List.append_nil,List.length_append,
    List.length_cons,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem first_fixed (A B : NormalForm P) (X Y Z T : List (NormalForm P))
    {E : NormalForm P} (v : At (BlockedMix.firstTag (.disj A B) X Y).erase E) :
    ((block A B X Y Z T).route.firstBlock.firstBlock.get
      ((BlockedMix.firstTag (.disj A B) X Y).retain v)).index ≠ (block A B X Y Z T).keep.index := by
  have hn := (BlockedMix.firstTag (.disj A B) X Y).retain_ne v
  have hi := ((BlockedMix.firstTag (.disj A B) X Y).retain v).index_lt
  rw [Route.firstBlock_get,Route.firstBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index,
    At.index_before,At.index_before]
  have hx : (BlockedMix.firstTag (.disj A B) X Y).index = X.length := by
    simp only [BlockedMix.firstTag,At.index_shift,At.index,Nat.add_zero]
  rw [hx] at hn
  simp only [List.length_append,List.length_cons] at hi
  simp only [block,gaps,List.append_nil,List.length_append,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem second_fixed (A B : NormalForm P) (X Y Z T : List (NormalForm P))
    {E : NormalForm P} (v : At (BlockedMix.firstTag (.disj A B) Z T).erase E) :
    ((block A B X Y Z T).route.firstBlock.secondBlock.get
      ((BlockedMix.firstTag (.disj A B) Z T).retain v)).index ≠ (block A B X Y Z T).keep.index := by
  have hn := (BlockedMix.firstTag (.disj A B) Z T).retain_ne v
  have hi := ((BlockedMix.firstTag (.disj A B) Z T).retain v).index_lt
  rw [Route.secondBlock_get,Route.firstBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index,
    At.index_before,At.index_shift]
  have hx : (BlockedMix.firstTag (.disj A B) Z T).index = Z.length := by
    simp only [BlockedMix.firstTag,At.index_shift,At.index,Nat.add_zero]
  rw [hx] at hn
  simp only [List.length_append,List.length_cons] at hi
  simp only [block,gaps,List.append_nil,List.length_append,List.length_cons,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

def firstResidue (A B : NormalForm P) (X Y Z T : List (NormalForm P)) :
    Route (block A B X Y Z T).keep.erase (BlockedMix.firstTag (.disj A B) X Y).erase :=
  Route.selectedResidual (block A B X Y Z T).route.firstBlock.firstBlock _ _ (first_fixed A B X Y Z T)

def secondResidue (A B : NormalForm P) (X Y Z T : List (NormalForm P)) :
    Route (block A B X Y Z T).keep.erase (BlockedMix.firstTag (.disj A B) Z T).erase :=
  Route.selectedResidual (block A B X Y Z T).route.firstBlock.secondBlock _ _ (second_fixed A B X Y Z T)

def parent {A B : NormalForm P} {X Y Z T D E : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E) :
    G P (gaps [X,Y++Z,T]++[.disj A B]) (D++E) :=
  (block A B X Y Z T).applyL (Nat.le_succ 2) _ (BlockedSource.disjLLast f g)

theorem parent_source {A B : NormalForm P} {X Y Z T D E : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E) :
    parent f g = BlockedSource.left3 (.disj A B) X (Y++Z) T [] (D++E)
      ((BlockedSource.disjLLast f g).reindex (by simp only [List.append_assoc,List.cons_append]) rfl) := by
  simp only [parent,block,ContractionBlock.applyL,BlockedSource.left3,G.reindex_trans]
  rfl

end DosenPetric.Reduced.Gentzen.BlockedDisjBoth
