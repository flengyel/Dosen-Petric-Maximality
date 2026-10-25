module

public import DosenPetric.GentzenParametricConjunction
public import DosenPetric.GentzenConjunctionBranchRanks
public import DosenPetric.GentzenHeadLogicalRankBounds
public import DosenPetric.GentzenNativeLogicalBoundCoordinates

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.ParametricConjunction
universe u
variable {P : Type u} {A B C : NormalForm P} {F K U L Γ Θ : List (NormalForm P)}
variable (p : ContractionSelection C F K) (q : ContractionSelection C U L)
variable (f : G P Γ (A::F)) (g : G P Θ (B::U))

theorem block_keep : (block (A:=A) (B:=B) p q).keep=.there (p.chain q).keep := by
  apply At.index_injective
  rw [ContractionBlock.keep_index,At.index,←p.merge_retained q,ContractionBlock.keep_index]
  simp only [gaps,List.length_append,List.length_cons,List.append_nil]
  omega

theorem block_selected : (block (A:=A) (B:=B) p q).selected=
    [.there (p.keep.before L),.there (At.shift K q.keep)] := by
  apply At.list_index_injective
  rw [ContractionBlock.selected_indices]
  simp only [block,copyOffsets,List.map_cons,List.map_nil,At.index,At.index_before,At.index_shift,
    List.length_cons,List.length_append,p.keep_index,q.keep_index]
  have hp:=p.lower_length
  simp only [gaps,List.length_append] at hp ⊢
  simp only [List.cons.injEq,true_and,and_true]
  omega

theorem old_rank : (old p q f g).rho .right (.there (p.chain q).keep)=
    1+(p.selected.map (fun a => f.rho .right (.there a))).sum+
      (q.selected.map (fun a => g.rho .right (.there a))).sum+p.arity+q.arity := by
  have hn : 2≤(ContractionSelection.fixed (.conj A B) (p.chain q)).arity := by
    change 2≤(p.chain q).arity
    rw [ContractionSelection.chain_count]
    have hp:=p.arity_pos; have hq:=q.arity_pos; omega
  let R : At (.conj A B::(p.erased++L)) C→Nat := fun a => (old p q f g).rho .right a
  let r : At (.conj A B::(F++U)) C→Nat := fun a => (G.conjR f g).rho .right a
  have h:=(ContractionSelection.fixed (.conj A B) (p.chain q)).performR_rank (Γ++Θ) (G.conjR f g)
  change R (.there (p.chain q).keep)=
    ((p.chain q).selected.map At.there |>.map r).sum+(if 2≤(ContractionSelection.fixed (.conj A B) (p.chain q)).arity then 1 else 0) at h
  rw [ite_eq_left hn,ContractionSelection.chain_selected] at h
  simp only [List.map_map,List.map_append,List.sum_append,Function.comp_def] at h
  change (old p q f g).rho .right (.there (p.chain q).keep)=
    (p.selected.map (fun a => (G.conjR f g).rho .right (.there (a.before U)))).sum+
      (q.selected.map (fun a => (G.conjR f g).rho .right (.there (At.shift F a)))).sum+1 at h
  simp only [G.rho_conjR_f,G.rho_conjR_g] at h
  rw [G.sum_map_one_add,G.sum_map_one_add,p.selected_length,q.selected_length] at h
  omega

theorem repair_rank : (repair p q f g).rho .right (.there (p.chain q).keep)=
    3+((p.prependFixed [A]).performR Γ f).rho .right (.there p.keep)+
      ((q.prependFixed [B]).performR Θ g).rho .right (.there q.keep) := by
  have hk:=(block (A:=A) (B:=B) p q).rankR_keep (Nat.le_refl 2) _ (middle p q f g)
  have hs:=(block (A:=A) (B:=B) p q).rankR_sum (Nat.le_refl 2) _ (middle p q f g)
  rw [block_keep] at hk
  let r : At (.conj A B::(K++L)) C→Nat := fun a => (middle p q f g).rho .right a
  change (block p q).rankR (Nat.le_refl 2) _ (middle p q f g)=1+((block p q).selected.map r).sum at hs
  rw [block_selected] at hs
  change (block p q).rankR (Nat.le_refl 2) _ (middle p q f g)=1+(r (.there (p.keep.before L))+
    (r (.there (At.shift K q.keep))+0)) at hs
  simp only [r,middle,G.rho_conjR_f,G.rho_conjR_g] at hs
  change (block p q).rankR (Nat.le_refl 2) _ (middle p q f g)=_ at hs
  change (repair p q f g).rho .right (.there (p.chain q).keep)=_ at hk
  omega

theorem endpoint_le : (repair p q f g).rho .right (.there (p.chain q).keep)≤
    (old p q f g).rho .right (.there (p.chain q).keep) := by
  rw [repair_rank,old_rank,W6.HeadRight.premise_rank,W6.HeadRight.premise_rank]
  have hp:=p.overhead_bound; have hq:=q.overhead_bound
  omega

end DosenPetric.Reduced.Gentzen.W5.ParametricConjunction
