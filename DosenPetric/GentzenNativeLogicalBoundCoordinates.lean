module

public import DosenPetric.GentzenNativeLogicalRanks
public import DosenPetric.GentzenSourceLogicalPositions

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionSelection
variable {C : NormalForm P} {F K : List (NormalForm P)}
theorem lower_length (p : ContractionSelection C F K) :
    K.length=(gaps p.gs).length+1+p.tail.length := by
  have h:=congrArg List.length p.lower
  simpa only [gaps,List.length_append,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.symm
end ContractionSelection
namespace W6.NativeLeft

theorem first_branch_index (i k l x y z : Nat) (h₀ : 0<i) (hi : i<k+1)
    (hk : k=x+1+y) (hm : i-1=x ∨ i-1=k+z ∨ i-1=k+l) : i=x+1 := by omega

theorem second_branch_index (i k l x y z t : Nat) (h₀ : 0<i) (hi : i<l+1)
    (hk : k=x+1+y) (hl : l=z+1+t)
    (hm : k+i-1=x ∨ k+i-1=k+z ∨ k+i-1=k+l) : i=z+1 := by omega
variable {A B : NormalForm P} {F K U L : List (NormalForm P)}
variable (p : ContractionSelection (.disj A B) F K) (q : ContractionSelection (.disj A B) U L)

theorem source_keep_index : (p.sourceKeep q).index=(gaps (W6.SourceLeft.tripleBlock p q).gs).length := by
  have h:=(p.sourceRetained q).keep_index
  rw [p.sourceRetained_keep q,p.sourceRetained_gs q] at h
  exact h

theorem triple_selected_index (i : Nat) :
    copyIndex (W6.SourceLeft.tripleBlock p q).gs i=(p.sourceKeep q).index ↔
      i=(gaps p.gs).length ∨ i=K.length+(gaps q.gs).length ∨ i=K.length+L.length := by
  rw [source_keep_index,copyIndex_selected]
  have hp:=p.lower_length
  have hq:=q.lower_length
  change i∈copyOffsets [gaps p.gs,p.tail++gaps q.gs,q.tail] ↔ _
  simp only [copyOffsets,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,
    List.length_append]
  simp only [gaps,List.length_append] at hp hq ⊢
  omega

theorem triple_fresh : (W6.SourceLeft.tripleBlock p q).route.get
    (At.shift (K++L) (.here (.disj A B) []))=p.sourceKeep q := by
  have hm : At.shift (K++L) (.here (.disj A B) [])∈(p.sourceRetained q).selected := by
    rw [p.sourceRetained_selected q]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have h:=((p.sourceRetained q).selected_iff _).mp hm
  rw [ContractionSelection.route_eq,W6.SourceLeft.triple_block,p.sourceRetained_keep q] at h
  exact h

theorem exit_retained : (exitRoute p q).get (p.sourceKeep q)=(p.chain q).keep := by
  have h:=exit_square p q (.here (.disj A B) (K++L))
  rw [Route.toTail_here,triple_fresh,ContractionBlock.selectedHead_route,Route.get] at h
  exact h.trans (p.merge_retained q)

theorem exit_index {D : NormalForm P} (a : At (source p q) D) :
    ((exitRoute p q).get a).index=exchangeIndex (base p q).length q.tail.length 1 a.index := by
  simp only [exitRoute,Route.get_cast,At.index_cast,Route.exchange_get,swapBlocks_index,List.length_singleton]

theorem exit_index_injective (i j : Nat)
    (h : exchangeIndex (base p q).length q.tail.length 1 i=
      exchangeIndex (base p q).length q.tail.length 1 j) : i=j := by
  have he:=congrArg (exchangeIndex (base p q).length 1 q.tail.length) h
  rwa [exchangeIndex_inverse,exchangeIndex_inverse] at he
end W6.NativeLeft
end DosenPetric.Reduced.Gentzen
