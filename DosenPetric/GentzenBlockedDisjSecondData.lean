module

public import DosenPetric.GentzenSequentialDisjSecondSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedDisjSecond
universe u
variable {P : Type u}

def block (A B : NormalForm P) (X Z T : List (NormalForm P)) :
    ContractionBlock P ((X++(Z++.disj A B::T))++[.disj A B]) (gaps [X++Z,T]++[.disj A B]) where
  C := .disj A B
  gs := [X++Z,T]
  tail := []
  upper := by simp only [repeated,List.append_assoc,List.cons_append,List.nil_append]
  lower := rfl

def parametric (A B : NormalForm P) (Z T : List (NormalForm P)) : At (Z++.disj A B::T) (.disj A B) :=
  BlockedMix.firstTag (.disj A B) Z T

theorem first_get (A B : NormalForm P) (X Z T : List (NormalForm P)) :
    (block A B X Z T).route.firstBlock.get (At.shift X (parametric A B Z T)) = (block A B X Z T).keep := by
  apply At.index_injective
  rw [Route.firstBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,parametric,BlockedMix.firstTag,At.index_before,At.index_shift,At.index,
    Nat.add_zero,gaps,List.append_nil,List.length_append,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem second_get (A B : NormalForm P) (X Z T : List (NormalForm P)) :
    (block A B X Z T).route.secondBlock.get (.here (.disj A B) []) = (block A B X Z T).keep := by
  apply At.index_injective
  rw [Route.secondBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,At.index_shift,At.index,Nat.add_zero,gaps,List.append_nil,List.length_append,
    List.length_nil,List.length_cons,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem first_fixed (A B : NormalForm P) (X Z T : List (NormalForm P))
    {E : NormalForm P} (v : At (At.shift X (parametric A B Z T)).erase E) :
    ((block A B X Z T).route.firstBlock.get ((At.shift X (parametric A B Z T)).retain v)).index ≠
      (block A B X Z T).keep.index := by
  have hn := (At.shift X (parametric A B Z T)).retain_ne v
  have hi := ((At.shift X (parametric A B Z T)).retain v).index_lt
  rw [Route.firstBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index,At.index_before]
  have hx : (At.shift X (parametric A B Z T)).index = X.length+Z.length := by
    simp only [parametric,BlockedMix.firstTag,At.index_shift,At.index,Nat.add_zero]
  rw [hx] at hn
  simp only [List.length_append,List.length_cons] at hi
  simp only [block,gaps,List.append_nil,List.length_append,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

def rawResidue (A B : NormalForm P) (X Z T : List (NormalForm P)) :
    Route (block A B X Z T).keep.erase (At.shift X (parametric A B Z T)).erase :=
  Route.selectedResidual (block A B X Z T).route.firstBlock (block A B X Z T).keep
    (At.shift X (parametric A B Z T)) (first_fixed A B X Z T)

def residue (A B : NormalForm P) (X Z T : List (NormalForm P)) :
    Route (block A B X Z T).keep.erase (X++(parametric A B Z T).erase) :=
  (rawResidue A B X Z T).cast rfl (At.erase_shift_at X (parametric A B Z T))

def parent {A B : NormalForm P} {X Z T D E : List (NormalForm P)}
    (f : G P (X++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E) :
    G P (gaps [X++Z,T]++[.disj A B]) (D++E) :=
  (block A B X Z T).applyL (Nat.le_refl 2) (D++E) (BlockedSource.disjLLast f g)

theorem parent_source {A B : NormalForm P} {X Z T D E : List (NormalForm P)}
    (f : G P (X++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E) :
    parent f g = BlockedSource.left2 (.disj A B) (X++Z) T [] (D++E)
      ((BlockedSource.disjLLast f g).reindex (by simp only [List.append_assoc,List.cons_append]) rfl) := by
  simp only [parent,block,ContractionBlock.applyL,BlockedSource.left2,G.reindex_trans]
  rfl

end DosenPetric.Reduced.Gentzen.BlockedDisjSecond
