module

public import DosenPetric.GentzenRotationInverses
public import DosenPetric.GentzenSelectedHeadBlock
public import DosenPetric.GentzenLengthCopyIndices

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W6.NativeLeft
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L : List (NormalForm P)}
variable (p : ContractionSelection (.disj A B) F K) (q : ContractionSelection (.disj A B) U L)

abbrev base := p.erased++gaps q.gs
abbrev source := p.erased++(q.erased++[.disj A B])
abbrev target (_q : ContractionSelection (.disj A B) U L) := p.erased++L

theorem exit_source : base p q++q.tail++[.disj A B]++[]=source p q := by
  unfold source base
  rw [q.erased_eq]
  simp only [List.append_nil,List.append_assoc]
theorem exit_target : base p q++[.disj A B]++q.tail++[]=target p q := by
  unfold target base
  calc
    _ = p.erased++(gaps q.gs++.disj A B::q.tail) := by
      simp only [List.append_nil,List.append_assoc,List.singleton_append]
    _ = _ := congrArg (fun Ξ => p.erased++Ξ) q.lower

def exitRoute : Route (target p q) (source p q) :=
  (Route.exchange (base p q) q.tail [.disj A B] []).cast (exit_target p q) (exit_source p q)

set_option maxHeartbeats 50000 in
theorem exit_square {D : NormalForm P} (a : At (.disj A B::(K++L)) D) :
    (exitRoute p q).get ((W6.SourceLeft.tripleBlock p q).route.get
      ((Route.toTail (K++L) (.disj A B)).get a))=
      (p.mergeBlock q).selectedHead.route.get a := by
  apply At.index_injective
  have hp : K.length=(gaps p.gs).length+1+p.tail.length := by
    have h:=congrArg List.length p.lower
    simpa only [gaps,List.length_append,List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h.symm
  have hq : L.length=(gaps q.gs).length+1+q.tail.length := by
    have h:=congrArg List.length q.lower
    simpa only [gaps,List.length_append,List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h.symm
  have he : p.erased.length=(gaps p.gs).length+p.tail.length := by
    exact (congrArg List.length p.erased_eq).trans (by rw [List.length_append])
  cases a with
  | here =>
    rw [Route.toTail_here]
    simp only [exitRoute,Route.get_cast,At.index_cast,Route.exchange_get,swapBlocks_index,
      ContractionBlock.get_index,W6.SourceLeft.tripleBlock,ContractionBlock.selectedHead,
      ContractionSelection.mergeBlock,At.index_shift,At.index,base,copyIndex_lengths,
      List.map_cons,List.map_nil,List.length_append,List.length_singleton,List.length_nil]
    rw [hp,hq,he]
    have hj : ((gaps p.gs).length+1+p.tail.length)+((gaps q.gs).length+1+q.tail.length)+0=
        (gaps p.gs).length+p.tail.length+(gaps q.gs).length+q.tail.length+2 := by omega
    rw [hj]
    simpa only [gaps,List.length_append,Nat.add_assoc] using
      lengthCopy_rotate_head (gaps p.gs).length p.tail.length (gaps q.gs).length q.tail.length
  | there a =>
    have hi : a.index<(gaps p.gs).length+p.tail.length+(gaps q.gs).length+q.tail.length+2 := by
      have h:=a.index_lt
      simp only [List.length_append] at h
      rw [hp,hq] at h
      omega
    rw [Route.toTail_there]
    simp only [exitRoute,Route.get_cast,At.index_cast,Route.exchange_get,swapBlocks_index,
      ContractionBlock.get_index,W6.SourceLeft.tripleBlock,ContractionBlock.selectedHead,
      ContractionSelection.mergeBlock,At.index_before,At.index,base,copyIndex_lengths,
      List.map_cons,List.map_nil,List.length_append,List.length_singleton,List.length_nil]
    rw [he]
    simpa only [gaps,List.length_append] using
      lengthCopy_rotate_tail (gaps p.gs).length p.tail.length (gaps q.gs).length q.tail.length a.index hi

theorem product_square : ofTerm (p.mergeBlock q).selectedHead.route.product=
    comp (ofTerm (exitRoute p q).product)
      (comp (ofTerm (W6.SourceLeft.tripleBlock p q).route.product)
        (ofTerm (Route.toTail (K++L) (.disj A B)).product)) := by
  apply product_positions
  intro D a
  rw [Route.product_get,Laws.assoc,Laws.assoc,Route.product_get,Route.product_get,Route.product_get,exit_square]

end DosenPetric.Reduced.Gentzen.W6.NativeLeft
