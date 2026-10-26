module

public import DosenPetric.GentzenSourceOneSingletons
public import DosenPetric.GentzenRetainedLastBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace Route

theorem identity_parallel (F U : List (NormalForm P)) :
    (identity F).parallel (identity U)=identity (F++U) := by
  apply ext_get
  intro A a
  cases At.cases_append F U a with
  | inl h => obtain ⟨a,rfl⟩:=h; rw [parallel_before,get_identity,get_identity]
  | inr h => obtain ⟨a,rfl⟩:=h; rw [parallel_shift,get_identity,get_identity]
end Route
namespace ContractionSelection
variable {C : NormalForm P} {F K : List (NormalForm P)}
variable (p : ContractionSelection C F K)

theorem terminal_retained_block : (p.retainChain (.last [])).block=p.retainedLastBlock := by
  apply ContractionBlock.ext_data
  · rfl
  · change (p.retainChain (.last [])).first::(p.retainChain (.last [])).rest=[gaps p.gs,p.tail]
    rw [p.retain_first,p.retain_rest]
    simp only [first,rest,List.append_nil]
  · exact p.retain_tail (.last [])

theorem terminal_factor (o : Op) :
    (p.chain (.last [])).route.sideArrow o=(side P o).comp
      (p.retainedLastBlock.route.sideArrow o)
      ((p.route.parallel (Route.identity [C])).sideArrow o) := by
  have h:=(p.extend [C]).fuse_side (p.retainChain (.last [])) (p.retain_member (.last [])) o
  rw [p.fuse_extend (.last []),(p.retainChain (.last [])).route_eq,p.terminal_retained_block,p.extend_route] at h
  exact h

theorem terminal_arity : 2≤(p.chain (.last [])).arity := by
  rw [p.chain_count]
  have h:=p.arity_pos
  change 2≤p.arity+1
  omega

theorem terminal_keep : (p.chain (.last [])).keep=p.lastKeep := p.chain_keep (.last [])

theorem terminal_selected : (p.chain (.last [])).selected=
    p.selected.map (fun a=>a.before [C])++[At.shift F (.here C [])] := by
  rw [p.chain_selected]
  rfl

theorem retainedLast_keep : p.retainedLastBlock.keep=p.lastKeep := by
  apply At.index_injective
  rw [ContractionBlock.keep_index,p.lastKeep_index]

theorem retainedLast_selected : p.retainedLastBlock.selected=
    [p.keep.before [C],At.shift K (.here C [])] := by
  apply At.list_index_injective
  rw [ContractionBlock.selected_indices]
  simp only [retainedLastBlock,copyOffsets,List.map_cons,List.map_nil,At.index_before,
    At.index_shift,At.index,Nat.add_zero,p.keep_index]
  have h:=p.lower_length
  simp only [gaps,List.length_append] at h ⊢
  simp only [List.cons.injEq,true_and,and_true]
  omega
end ContractionSelection
end DosenPetric.Reduced.Gentzen
