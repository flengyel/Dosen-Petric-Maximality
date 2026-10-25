module

public import DosenPetric.GentzenHeadLogicalBlocked
public import DosenPetric.GentzenConjunctionBranchRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W6.HeadRight
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L Γ Θ : List (NormalForm P)}
variable (p : ContractionSelection (.conj A B) F K) (q : ContractionSelection (.conj A B) U L)
variable (f : G P Γ (A::F)) (g : G P Θ (B::U))

def premiseSum : Nat := (p.selected.map (fun a => f.rho .right (.there a))).sum+
  (q.selected.map (fun a => g.rho .right (.there a))).sum

theorem old_rank : (old p q f g).rho .right (p.chain q).keep=
    premiseSum p q f g+p.arity+q.arity+2 := by
  have hn : 2≤(ContractionSelection.more (p.chain q)).arity := by
    change 2≤(p.chain q).arity+1
    rw [ContractionSelection.chain_count]
    have hp:=p.arity_pos; have hq:=q.arity_pos; omega
  let R : At (p.erased++L) (.conj A B)→Nat := fun a => (old p q f g).rho .right a
  let r : At (.conj A B::(F++U)) (.conj A B)→Nat := fun a => (G.conjR f g).rho .right a
  have h:=(ContractionSelection.more (p.chain q)).performR_rank (Γ++Θ) (G.conjR f g)
  change R (p.chain q).keep=((ContractionSelection.more (p.chain q)).selected.map r).sum+
    (if 2≤(ContractionSelection.more (p.chain q)).arity then 1 else 0) at h
  rw [ite_eq_left hn] at h
  change R (p.chain q).keep=((At.here (.conj A B) (F++U)::(p.chain q).selected.map At.there).map r).sum+1 at h
  rw [ContractionSelection.chain_selected] at h
  simp only [List.map_cons,List.map_map,List.map_append,List.sum_cons,List.sum_append,Function.comp_def] at h
  change (old p q f g).rho .right (p.chain q).keep=
    (G.conjR f g).rho .right (.here (.conj A B) (F++U))+
      ((p.selected.map (fun a => (G.conjR f g).rho .right (.there (a.before U)))).sum+
      (q.selected.map (fun a => (G.conjR f g).rho .right (.there (At.shift F a)))).sum)+1 at h
  simp only [G.rho_conjR_principal,G.rho_conjR_f,G.rho_conjR_g] at h
  rw [G.sum_map_one_add,G.sum_map_one_add,p.selected_length,q.selected_length] at h
  unfold premiseSum
  omega

theorem repair_rank : (repair p q f g).rho .right (p.chain q).keep=
    4+((p.prependFixed [A]).performR Γ f).rho .right (.there p.keep)+
      ((q.prependFixed [B]).performR Θ g).rho .right (.there q.keep) := by
  have hk:=(p.mergeBlock q).selectedHead.rankR_keep (middle_bound p q) _ (middle p q f g)
  have hs:=(p.mergeBlock q).selectedHead.rankR_sum (middle_bound p q) _ (middle p q f g)
  rw [ContractionBlock.selectedHead_keep,p.merge_retained q] at hk
  let r : At (.conj A B::(K++L)) (.conj A B)→Nat := fun a => (middle p q f g).rho .right a
  change (p.mergeBlock q).selectedHead.rankR (middle_bound p q) _ (middle p q f g)=
    1+((p.mergeBlock q).selectedHead.selected.map r).sum at hs
  rw [ContractionBlock.selectedHead_selected,p.merge_selected q] at hs
  change (p.mergeBlock q).selectedHead.rankR (middle_bound p q) _ (middle p q f g)=
    1+(r (.here (.conj A B) (K++L))+(r (.there (p.keep.before L))+
      (r (.there (At.shift K q.keep))+0))) at hs
  simp only [r,middle,G.rho_conjR_principal,G.rho_conjR_f,G.rho_conjR_g] at hs
  change (repair p q f g).rho .right (p.chain q).keep=_ at hk
  change (p.mergeBlock q).selectedHead.rankR (middle_bound p q) _ (middle p q f g)=_ at hs
  omega

theorem premise_rank {C : NormalForm P} {F K Γ : List (NormalForm P)}
    (p : ContractionSelection C F K) (A : NormalForm P) (f : G P Γ (A::F)) :
    ((p.prependFixed [A]).performR Γ f).rho .right (.there p.keep)=
      (p.selected.map (fun a => f.rho .right (.there a))).sum+(if 2≤p.arity then 1 else 0) := by
  let R : At (A::K) C→Nat := fun a => ((p.prependFixed [A]).performR Γ f).rho .right a
  let r : At (A::F) C→Nat := fun a => f.rho .right a
  have h:=(p.prependFixed [A]).performR_rank Γ f
  change R (p.prependFixed [A]).keep=((p.prependFixed [A]).selected.map r).sum+
    (if 2≤(p.prependFixed [A]).arity then 1 else 0) at h
  rw [p.prepend_keep,p.prepend_selected,p.prepend_arity] at h
  simpa only [List.map_map,Function.comp_def,At.shift,List.nil_append,R,r] using h

theorem endpoint_le : (repair p q f g).rho .right (p.chain q).keep≤
    (old p q f g).rho .right (p.chain q).keep := by
  rw [repair_rank,old_rank,premise_rank,premise_rank]
  have hp:=p.overhead_bound; have hq:=q.overhead_bound
  unfold premiseSum
  omega

end DosenPetric.Reduced.Gentzen.W6.HeadRight
