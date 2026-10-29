module

public import DosenPetric.GentzenSequentialConjBothSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedConjBoth
universe u
variable {P : Type u}

def block (A B : NormalForm P) (X Y Z T : List (NormalForm P)) :
    ContractionBlock P (.conj A B::((X++.conj A B::Y)++(Z++.conj A B::T)))
      (gaps [[],X,Y++Z]++.conj A B::T) where
  C := .conj A B
  gs := [[],X,Y++Z]
  tail := T
  upper := by simp only [repeated,List.append_assoc,List.cons_append,List.nil_append]
  lower := rfl

theorem fresh_get (A B : NormalForm P) (X Y Z T : List (NormalForm P)) :
    (block A B X Y Z T).route.get (.here (.conj A B) ((X++.conj A B::Y)++(Z++.conj A B::T))) =
      (block A B X Y Z T).keep := by
  apply At.index_injective
  rw [ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,At.index,gaps,List.append_nil,List.nil_append,List.length_nil,List.length_append,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem first_get (A B : NormalForm P) (X Y Z T : List (NormalForm P)) :
    ((block A B X Y Z T).route.secondBlock (F:=[.conj A B])).firstBlock.get
      (BlockedMix.firstTag (.conj A B) X Y) = (block A B X Y Z T).keep := by
  apply At.index_injective
  rw [Route.firstBlock_get,Route.secondBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,BlockedMix.firstTag,At.index_before,At.index_shift,At.index,Nat.add_zero,
    gaps,List.append_nil,List.nil_append,List.length_append,List.length_cons,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem second_get (A B : NormalForm P) (X Y Z T : List (NormalForm P)) :
    ((block A B X Y Z T).route.secondBlock (F:=[.conj A B])).secondBlock.get
      (BlockedMix.firstTag (.conj A B) Z T) = (block A B X Y Z T).keep := by
  apply At.index_injective
  rw [Route.secondBlock_get,Route.secondBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,BlockedMix.firstTag,At.index_shift,At.index,Nat.add_zero,gaps,List.append_nil,
    List.nil_append,List.length_append,List.length_cons,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem first_fixed (A B : NormalForm P) (X Y Z T : List (NormalForm P))
    {E : NormalForm P} (v : At (BlockedMix.firstTag (.conj A B) X Y).erase E) :
    (((block A B X Y Z T).route.secondBlock (F:=[.conj A B])).firstBlock.get
      ((BlockedMix.firstTag (.conj A B) X Y).retain v)).index ≠ (block A B X Y Z T).keep.index := by
  have hn := (BlockedMix.firstTag (.conj A B) X Y).retain_ne v
  have hi := ((BlockedMix.firstTag (.conj A B) X Y).retain v).index_lt
  rw [Route.firstBlock_get,Route.secondBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index,
    At.index_shift,At.index_before]
  have hx : (BlockedMix.firstTag (.conj A B) X Y).index = X.length := by
    simp only [BlockedMix.firstTag,At.index_shift,At.index,Nat.add_zero]
  rw [hx] at hn
  simp only [List.length_append,List.length_cons] at hi
  simp only [block,gaps,List.append_nil,List.nil_append,List.length_append,List.length_cons,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem second_fixed (A B : NormalForm P) (X Y Z T : List (NormalForm P))
    {E : NormalForm P} (v : At (BlockedMix.firstTag (.conj A B) Z T).erase E) :
    (((block A B X Y Z T).route.secondBlock (F:=[.conj A B])).secondBlock.get
      ((BlockedMix.firstTag (.conj A B) Z T).retain v)).index ≠ (block A B X Y Z T).keep.index := by
  have hn := (BlockedMix.firstTag (.conj A B) Z T).retain_ne v
  have hi := ((BlockedMix.firstTag (.conj A B) Z T).retain v).index_lt
  rw [Route.secondBlock_get,Route.secondBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index,
    At.index_shift,At.index_shift]
  have hx : (BlockedMix.firstTag (.conj A B) Z T).index = Z.length := by
    simp only [BlockedMix.firstTag,At.index_shift,At.index,Nat.add_zero]
  rw [hx] at hn
  simp only [List.length_append,List.length_cons] at hi
  simp only [block,gaps,List.append_nil,List.nil_append,List.length_append,List.length_cons,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

def firstResidue (A B : NormalForm P) (X Y Z T : List (NormalForm P)) :
    Route (block A B X Y Z T).keep.erase (BlockedMix.firstTag (.conj A B) X Y).erase :=
  Route.selectedResidual ((block A B X Y Z T).route.secondBlock (F:=[.conj A B])).firstBlock _ _
    (first_fixed A B X Y Z T)

def secondResidue (A B : NormalForm P) (X Y Z T : List (NormalForm P)) :
    Route (block A B X Y Z T).keep.erase (BlockedMix.firstTag (.conj A B) Z T).erase :=
  Route.selectedResidual ((block A B X Y Z T).route.secondBlock (F:=[.conj A B])).secondBlock _ _
    (second_fixed A B X Y Z T)

def parent {A B : NormalForm P} {Γ Θ X Y Z T : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::(Z++.conj A B::T))) :
    G P (Γ++Θ) (gaps [[],X,Y++Z]++.conj A B::T) :=
  (block A B X Y Z T).applyR (Nat.le_succ 2) _ (G.conjR f g)

theorem parent_source {A B : NormalForm P} {Γ Θ X Y Z T : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::(Z++.conj A B::T))) :
    parent f g = BlockedSource.right3 (.conj A B) (Γ++Θ) [] X (Y++Z) T
      ((G.conjR f g).reindex rfl (by simp only [List.nil_append,List.append_assoc,List.cons_append])) := by
  simp only [parent,block,ContractionBlock.applyR,BlockedSource.right3,G.reindex_trans]
  rfl

end DosenPetric.Reduced.Gentzen.BlockedConjBoth
