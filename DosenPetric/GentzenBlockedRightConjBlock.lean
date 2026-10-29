module

public import DosenPetric.GentzenBlockedRightConjSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedRightConj
universe u
variable {P : Type u}

def gammaBlock (A B C : NormalForm P) (X Y Z T : List (NormalForm P)) :
    ContractionBlock P (.conj A B::((X++C::Y)++(Z++C::T)))
      (.conj A B::(gaps [X,Y++Z]++C::T)) where
  C := C
  gs := [.conj A B::X,Y++Z]
  tail := T
  upper := by simp only [repeated,List.append_assoc,List.cons_append,List.nil_append]
  lower := by simp only [gaps,List.append_nil,List.cons_append]

theorem gammaBlock_route (A B C : NormalForm P) (X Y Z T : List (NormalForm P)) :
    (gammaBlock A B C X Y Z T).route = ((BlockedMix.gammaBlock C Z T X Y).route).head (.conj A B) := by
  apply Route.ext_get
  intro V a
  apply At.index_injective
  cases a with
  | here =>
    rw [ContractionBlock.get_index,Route.head_here]
    simp only [gammaBlock,copyIndex,List.length_cons,Nat.zero_lt_succ,ite_true,At.index]
  | there a =>
    rw [ContractionBlock.get_index,Route.head_there]
    change copyIndex ((.conj A B::X)::[Y++Z]) (a.index+1) =
      (((BlockedMix.gammaBlock C Z T X Y).route).get a).index+1
    rw [ContractionSelection.copyIndex_front,ContractionBlock.get_index]
    rfl

theorem gammaBlock_keep (A B C : NormalForm P) (X Y Z T : List (NormalForm P)) :
    (gammaBlock A B C X Y Z T).keep = .there (BlockedMix.gammaBlock C Z T X Y).keep := by
  apply At.index_injective
  rw [ContractionBlock.keep_index]
  change (gaps [.conj A B::X,Y++Z]).length = (BlockedMix.gammaBlock C Z T X Y).keep.index+1
  rw [ContractionBlock.keep_index]
  simp only [BlockedMix.gammaBlock,gaps,List.length_append,List.length_cons,List.length_nil]
  omega

end DosenPetric.Reduced.Gentzen.BlockedRightConj
