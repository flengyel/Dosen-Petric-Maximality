module

public import DosenPetric.GentzenOneHeadDisjunctionRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionSelection
universe u
variable {P : Type u} {C : NormalForm P} {F K Δ : List (NormalForm P)}
variable (p : ContractionSelection C F K)

def lastKeep : At (p.erased++[C]) C := At.shift p.erased (.here C [])

theorem lastKeep_index : p.lastKeep.index=(gaps p.retainedLastBlock.gs).length := by
  simp only [lastKeep,At.index_shift,At.index,Nat.add_zero,gaps,List.append_nil]
  exact congrArg List.length p.erased_eq

theorem last_selected_index (i : Nat) : copyIndex p.retainedLastBlock.gs i=p.lastKeep.index ↔
    i=p.keep.index ∨ i=K.length := by
  rw [p.lastKeep_index,copyIndex_selected,p.keep_index]
  change i∈copyOffsets [gaps p.gs,p.tail] ↔ _
  simp only [copyOffsets,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false]
  have hk:=p.lower_length
  omega

theorem last_exit_keep : p.retainedExit.get p.lastKeep=p.keep := by
  have h:=p.retainedExit_square (.here C K)
  rw [Route.toTail_here,p.retainedHead_route] at h
  change p.retainedExit.get (p.retainedLastBlock.route.get (At.shift K (.here C [])))=p.keep at h
  have hm : p.retainedLastBlock.route.get (At.shift K (.here C []))=p.lastKeep := by
    apply At.index_injective
    rw [ContractionBlock.get_index,At.index_shift,At.index,Nat.add_zero]
    exact (p.last_selected_index K.length).mpr (Or.inr rfl)
  rwa [hm] at h

theorem return_bound {k : Nat} (f : G P (p.erased++[C]) Δ)
    (h : ContractionBound .left C k f (fun x=>x.index=p.lastKeep.index)) :
    ContractionBound .left C k (p.retainedReturn f) (fun x=>x.index=p.keep.index) := by
  unfold retainedReturn
  apply UnaryCast.exchangeL_bound (gaps p.gs) p.tail [C] [] _ _ Δ f (fun i=>i=p.keep.index)
  apply h.mono
  intro x hx
  change exchangeIndex (gaps p.gs).length p.tail.length 1 x.index=p.keep.index at hx
  have he:=congrArg At.index p.last_exit_keep
  simp only [retainedExit,Route.get_cast,At.index_cast,Route.exchange_get,swapBlocks_index,List.length_singleton] at he
  have hi:=congrArg (exchangeIndex (gaps p.gs).length 1 p.tail.length) (hx.trans he.symm)
  simpa only [exchangeIndex_inverse] using hi
end DosenPetric.Reduced.Gentzen.ContractionSelection
