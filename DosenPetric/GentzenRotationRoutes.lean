module

public import DosenPetric.GentzenHeadRoutes

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.Route
universe u
variable {P : Type u} {F K : List (NormalForm P)}

def toHead (F : List (NormalForm P)) (A : NormalForm P) : Route (A::F) (F++[A]) :=
  (exchange [] F [A] []).cast
    (by simp only [List.nil_append,List.singleton_append,List.append_nil])
    (by simp only [List.nil_append,List.append_nil])
def toTail (F : List (NormalForm P)) (A : NormalForm P) : Route (F++[A]) (A::F) :=
  (exchange [] [A] F []).cast
    (by simp only [List.nil_append,List.append_nil])
    (by simp only [List.nil_append,List.singleton_append,List.append_nil])

theorem toHead_before (A : NormalForm P) {B : NormalForm P} (a : At F B) :
    (toHead F A).get (a.before [A])=.there a := by
  apply At.index_injective
  simp only [toHead,get_cast,exchange_get,At.index_cast,swapBlocks_index,
    At.index_before,At.index,List.length_nil,List.length_singleton,exchangeIndex,Nat.zero_add]
  have hi:=a.index_lt
  split <;> (try split) <;> (try split) <;> omega

theorem toHead_last (F : List (NormalForm P)) (A : NormalForm P) :
    (toHead F A).get (At.shift F (.here A []))=.here A F := by
  apply At.index_injective
  simp only [toHead,get_cast,exchange_get,At.index_cast,swapBlocks_index,
    At.index_shift,At.index,List.length_nil,List.length_singleton,exchangeIndex,Nat.zero_add]
  split <;> (try split) <;> (try split) <;> omega

theorem toTail_here (F : List (NormalForm P)) (A : NormalForm P) :
    (toTail F A).get (.here A F)=At.shift F (.here A []) := by
  apply At.index_injective
  simp only [toTail,get_cast,exchange_get,At.index_cast,swapBlocks_index,
    At.index_shift,At.index,List.length_nil,List.length_singleton,exchangeIndex,Nat.zero_add]
  simp

theorem toTail_there (A : NormalForm P) {B : NormalForm P} (a : At F B) :
    (toTail F A).get (.there a)=a.before [A] := by
  apply At.index_injective
  simp only [toTail,get_cast,exchange_get,At.index_cast,swapBlocks_index,
    At.index_before,At.index,List.length_nil,List.length_singleton,exchangeIndex,Nat.zero_add]
  have hi:=a.index_lt
  split <;> (try split) <;> (try split) <;> omega

theorem head_rotation (o : Op) (A : NormalForm P) (p : Route K F) :
    (side P o).comp ((p.head A).sideArrow o) ((toHead F A).sideArrow o) =
    (side P o).comp ((toHead K A).sideArrow o) ((p.parallel (identity [A])).sideArrow o) := by
  let C:=side P o
  apply side_ext o
  intro B a
  rw [C.assoc,sideArrow_get,C.assoc,sideArrow_get]
  cases At.cases_append F [A] a with
  | inl h =>
    obtain ⟨a,rfl⟩:=h
    rw [toHead_before,sideArrow_get,head_there,parallel_before,sideArrow_get,toHead_before]
  | inr h =>
    obtain ⟨a,rfl⟩:=h
    cases a with
    | here =>
      rw [toHead_last,sideArrow_get,head_here,parallel_shift,get_identity,sideArrow_get,toHead_last]
    | there a => cases a

theorem tail_rotation (o : Op) (A : NormalForm P) (p : Route K F) :
    (side P o).comp ((p.parallel (identity [A])).sideArrow o) ((toTail F A).sideArrow o) =
    (side P o).comp ((toTail K A).sideArrow o) ((p.head A).sideArrow o) := by
  let C:=side P o
  apply side_ext o
  intro B a
  rw [C.assoc,sideArrow_get,C.assoc,sideArrow_get]
  cases a with
  | here => rw [toTail_here,sideArrow_get,parallel_shift,get_identity,head_here,sideArrow_get,toTail_here]
  | there a => rw [toTail_there,sideArrow_get,parallel_before,head_there,sideArrow_get,toTail_there]

end DosenPetric.Reduced.Gentzen.Route
