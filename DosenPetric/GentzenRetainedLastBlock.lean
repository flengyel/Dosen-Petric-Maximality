module

public import DosenPetric.GentzenRetainedHeadBlock
public import DosenPetric.GentzenLengthCopyIndices
public import DosenPetric.GentzenNativeLogicalBoundCoordinates

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem lengthCopy_two_last (x t : Nat) : lengthCopy [x,t] (x+t+1)=x+t := by
  rw [lengthCopy_after _ _ _ (by omega)]
  have he : x+t+1-x-1=t := by omega
  rw [he,lengthCopy_here]
  simp only [List.sum_nil,Nat.add_zero]

theorem lengthCopy_two_rotate (x t i : Nat) (hi : i<x+t+1) :
    exchangeIndex x t 1 (lengthCopy [x,t] i)=lengthCopy [0,x] (i+1) := by
  rw [lengthCopy_after _ _ _ (Nat.zero_lt_succ i)]
  have he : i+1-0-1=i := by omega
  simp only [Nat.zero_add] at he ⊢
  rw [he]
  by_cases h₀ : i<x
  · rw [lengthCopy_before _ _ _ h₀,lengthCopy_before _ _ _ h₀,exchange_before_tail _ _ _ h₀]
  · by_cases h₁ : i=x
    · subst i
      rw [lengthCopy_here,lengthCopy_here]
      simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
      rw [exchange_last_tail]
    · have hx : x<i := by omega
      rw [lengthCopy_after _ _ _ hx,lengthCopy_after _ _ _ hx]
      have ht : i-x-1<t := by omega
      rw [lengthCopy_before _ _ _ ht]
      change exchangeIndex x t 1 (x+(i-x-1))=x+((i-x-1)+1)
      rw [exchange_inside_tail _ _ _ ht]
      omega

namespace ContractionSelection
variable {C : NormalForm P} {F K : List (NormalForm P)}
variable (p : ContractionSelection C F K)
abbrev retainedLastBlock : ContractionBlock P (K++[C]) (p.erased++[C]) where
  C:=C
  gs:=[gaps p.gs,p.tail]
  tail:=[]
  upper:=by
    calc
      _ = (gaps p.gs++C::p.tail)++[C] := by
        simp only [repeated,List.append_nil,List.append_assoc,List.cons_append]
      _ = _ := congrArg (fun Ξ=>Ξ++[C]) p.lower
  lower:=by simp only [gaps,List.append_nil]; rw [p.erased_eq]

theorem retainedLast_bound : 2≤p.retainedLastBlock.gs.length := Nat.le_refl 2

def retainedExit : Route K (p.erased++[C]) :=
  (Route.exchange (gaps p.gs) p.tail [C] []).cast
    (by simpa only [List.append_assoc,List.singleton_append,List.append_nil] using p.lower)
    (by rw [p.erased_eq]; simp only [List.append_assoc,List.append_nil])

theorem retainedExit_square {D : NormalForm P} (a : At (C::K) D) :
    p.retainedExit.get (p.retainedLastBlock.route.get ((Route.toTail K C).get a))=
      p.retainedHeadBlock.route.get a := by
  apply At.index_injective
  have hk:=p.lower_length
  cases a with
  | here =>
    rw [Route.toTail_here]
    simp only [retainedExit,Route.get_cast,At.index_cast,Route.exchange_get,swapBlocks_index,
      ContractionBlock.get_index,retainedLastBlock,retainedHeadBlock,At.index_shift,At.index,
      copyIndex_lengths,List.map_cons,List.map_nil,List.length_nil,List.length_singleton]
    rw [hk]
    have he : (gaps p.gs).length+1+p.tail.length+0=(gaps p.gs).length+p.tail.length+1 := by omega
    rw [he,lengthCopy_two_last,exchange_last_tail,lengthCopy_here]
    simp only [List.sum_cons,List.sum_nil,Nat.zero_add,Nat.add_zero]
  | there a =>
    rw [Route.toTail_there]
    simp only [retainedExit,Route.get_cast,At.index_cast,Route.exchange_get,swapBlocks_index,
      ContractionBlock.get_index,retainedLastBlock,retainedHeadBlock,At.index_before,At.index,
      copyIndex_lengths,List.map_cons,List.map_nil,List.length_nil,List.length_singleton]
    exact lengthCopy_two_rotate _ _ a.index (by have h:=a.index_lt; rw [hk] at h; omega)

theorem retainedExit_product : ofTerm p.retainedHeadBlock.route.product=
    comp (ofTerm p.retainedExit.product)
      (comp (ofTerm p.retainedLastBlock.route.product) (ofTerm (Route.toTail K C).product)) := by
  apply product_positions
  intro D a
  rw [Route.product_get,Laws.assoc,Laws.assoc,Route.product_get,Route.product_get,Route.product_get,p.retainedExit_square]
end ContractionSelection
end DosenPetric.Reduced.Gentzen
