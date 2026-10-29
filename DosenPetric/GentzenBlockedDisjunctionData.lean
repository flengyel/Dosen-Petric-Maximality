module

public import DosenPetric.GentzenSequentialDisjunctionSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedDisjunction
universe u
variable {P : Type u}

def block (A B : NormalForm P) (X Y : List (NormalForm P)) :
    ContractionBlock P (.disj A B::(X++.disj A B::Y)) (gaps [[],X]++.disj A B::Y) where
  C := .disj A B
  gs := [[],X]
  tail := Y
  upper := by simp only [repeated,List.append_assoc,List.cons_append,List.nil_append]
  lower := rfl

def parametric (A B : NormalForm P) (X Y : List (NormalForm P)) : At (X++.disj A B::Y) (.disj A B) :=
  BlockedMix.firstTag (.disj A B) X Y

theorem fresh_get (A B : NormalForm P) (X Y : List (NormalForm P)) :
    (block A B X Y).route.get (.here (.disj A B) (X++.disj A B::Y)) = (block A B X Y).keep := by
  apply At.index_injective
  rw [ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,At.index,gaps,List.append_nil,List.nil_append,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem parametric_get (A B : NormalForm P) (X Y : List (NormalForm P)) :
    (block A B X Y).route.get (.there (parametric A B X Y)) = (block A B X Y).keep := by
  apply At.index_injective
  rw [ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,parametric,BlockedMix.firstTag,At.index_shift,At.index,Nat.add_zero,
    gaps,List.append_nil,List.nil_append,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem retained_fixed (A B : NormalForm P) (X Y : List (NormalForm P))
    {E : NormalForm P} (v : At (parametric A B X Y).erase E) :
    ((block A B X Y).route.get (.there ((parametric A B X Y).retain v))).index ≠
      (block A B X Y).keep.index := by
  have hn := (parametric A B X Y).retain_ne v
  have hi := ((parametric A B X Y).retain v).index_lt
  have hx : (parametric A B X Y).index = X.length := by
    simp only [parametric,BlockedMix.firstTag,At.index_shift,At.index,Nat.add_zero]
  rw [hx] at hn
  rw [ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [List.length_append,List.length_cons] at hi
  simp only [block,At.index,gaps,List.append_nil,List.nil_append,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

def residue (A B : NormalForm P) (X Y : List (NormalForm P)) :
    Route (block A B X Y).keep.erase (parametric A B X Y).erase :=
  Route.selectedResidual
    (Route.secondBlock (F:=[.disj A B]) (U:=X++.disj A B::Y) (block A B X Y).route) (block A B X Y).keep
    (parametric A B X Y) (fun v => by
      simpa only [Route.secondBlock_get,At.shift] using retained_fixed A B X Y v)

theorem residue_retained (A B : NormalForm P) (X Y : List (NormalForm P))
    {E : NormalForm P} (v : At (parametric A B X Y).erase E) :
    (block A B X Y).route.get (.there ((parametric A B X Y).retain v)) =
      (block A B X Y).keep.retain ((residue A B X Y).get v) := by
  have he := Route.selectedResidual_get
    (Route.secondBlock (F:=[.disj A B]) (U:=X++.disj A B::Y) (block A B X Y).route)
    (block A B X Y).keep (parametric A B X Y)
    (fun v => by simpa only [Route.secondBlock_get,At.shift] using retained_fixed A B X Y v) v
  simpa only [residue,Route.secondBlock_get,At.shift] using he.symm

def parent {A B : NormalForm P} {F X Y : List (NormalForm P)}
    (f : G P F (A::B::(X++.disj A B::Y))) : G P F (gaps [[],X]++.disj A B::Y) :=
  (block A B X Y).applyR (Nat.le_refl 2) F (G.disjR F [] (X++.disj A B::Y) A B f)

theorem parent_source {A B : NormalForm P} {F X Y : List (NormalForm P)}
    (f : G P F (A::B::(X++.disj A B::Y))) :
    parent f = BlockedSource.right2 (.disj A B) F [] X Y (G.disjR F [] (X++.disj A B::Y) A B f) := by
  simp only [parent,block,ContractionBlock.applyR,BlockedSource.right2]
  rfl

def nativeChild {A B : NormalForm P} {F X Y : List (NormalForm P)}
    (f : G P F (A::B::(X++.disj A B::Y))) : G P F (.disj A B::A::B::(parametric A B X Y).erase) :=
  (LogicalDeletion.headUnder [] [A,B] (parametric A B X Y)).structural.right f

end DosenPetric.Reduced.Gentzen.BlockedDisjunction
