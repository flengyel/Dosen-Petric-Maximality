module

public import DosenPetric.GentzenSequentialConjSecondSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedConjSecond
universe u
variable {P : Type u}

def block (A B : NormalForm P) (F Z T : List (NormalForm P)) :
    ContractionBlock P (.conj A B::(F++(Z++.conj A B::T)))
      (gaps [[],F++Z]++.conj A B::T) where
  C := .conj A B
  gs := [[],F++Z]
  tail := T
  upper := by simp only [repeated,List.append_assoc,List.cons_append,List.nil_append]
  lower := rfl

def parametric (A B : NormalForm P) (Z T : List (NormalForm P)) : At (Z++.conj A B::T) (.conj A B) :=
  BlockedMix.firstTag (.conj A B) Z T

theorem fresh_get (A B : NormalForm P) (F Z T : List (NormalForm P)) :
    (block A B F Z T).route.get (.here (.conj A B) (F++(Z++.conj A B::T))) =
      (block A B F Z T).keep := by
  apply At.index_injective
  rw [ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,At.index,gaps,List.append_nil,List.nil_append,List.length_nil,List.length_append,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem parametric_get (A B : NormalForm P) (F Z T : List (NormalForm P)) :
    (block A B F Z T).route.get (.there (At.shift F (parametric A B Z T))) = (block A B F Z T).keep := by
  apply At.index_injective
  rw [ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,parametric,BlockedMix.firstTag,At.index_shift,At.index,Nat.add_zero,
    gaps,List.append_nil,List.nil_append,List.length_nil,List.length_append,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem retained_fixed (A B : NormalForm P) (F Z T : List (NormalForm P))
    {E : NormalForm P} (v : At (At.shift F (parametric A B Z T)).erase E) :
    ((block A B F Z T).route.get (.there ((At.shift F (parametric A B Z T)).retain v))).index ≠
      (block A B F Z T).keep.index := by
  have hn := (At.shift F (parametric A B Z T)).retain_ne v
  have hx : (At.shift F (parametric A B Z T)).index = F.length+Z.length := by
    simp only [parametric,BlockedMix.firstTag,At.index_shift,At.index,Nat.add_zero]
  rw [hx] at hn
  rw [ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [block,At.index,gaps,List.append_nil,List.nil_append,List.length_nil,List.length_append,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

def rawResidue (A B : NormalForm P) (F Z T : List (NormalForm P)) :
    Route (block A B F Z T).keep.erase (At.shift F (parametric A B Z T)).erase :=
  Route.selectedResidual (Route.secondBlock (F:=[.conj A B]) (U:=F++(Z++.conj A B::T))
    (block A B F Z T).route) (block A B F Z T).keep (At.shift F (parametric A B Z T))
    (fun v => by simpa only [Route.secondBlock_get,At.shift] using retained_fixed A B F Z T v)

def residue (A B : NormalForm P) (F Z T : List (NormalForm P)) :
    Route (block A B F Z T).keep.erase (F++(parametric A B Z T).erase) :=
  (rawResidue A B F Z T).cast rfl (At.erase_shift_at F (parametric A B Z T))

theorem rawResidue_retained (A B : NormalForm P) (F Z T : List (NormalForm P))
    {E : NormalForm P} (v : At (At.shift F (parametric A B Z T)).erase E) :
    (block A B F Z T).route.get (.there ((At.shift F (parametric A B Z T)).retain v)) =
      (block A B F Z T).keep.retain ((rawResidue A B F Z T).get v) := by
  have he := Route.selectedResidual_get
    (Route.secondBlock (F:=[.conj A B]) (U:=F++(Z++.conj A B::T)) (block A B F Z T).route)
    (block A B F Z T).keep (At.shift F (parametric A B Z T))
    (fun v => by simpa only [Route.secondBlock_get,At.shift] using retained_fixed A B F Z T v) v
  simpa only [rawResidue,Route.secondBlock_get,At.shift] using he.symm

def parent {A B : NormalForm P} {Γ Θ Z T F : List (NormalForm P)}
    (f : G P Γ (A::F)) (g : G P Θ (B::(Z++.conj A B::T))) :
    G P (Γ++Θ) (gaps [[],F++Z]++.conj A B::T) :=
  (block A B F Z T).applyR (Nat.le_refl 2) _ (G.conjR f g)

theorem parent_source {A B : NormalForm P} {Γ Θ Z T F : List (NormalForm P)}
    (f : G P Γ (A::F)) (g : G P Θ (B::(Z++.conj A B::T))) :
    parent f g = BlockedSource.right2 (.conj A B) (Γ++Θ) [] (F++Z) T
      ((G.conjR f g).reindex rfl (by simp only [List.nil_append,List.append_assoc])) := by
  simp only [parent,block,ContractionBlock.applyR,BlockedSource.right2,G.reindex_trans]
  rfl

end DosenPetric.Reduced.Gentzen.BlockedConjSecond
