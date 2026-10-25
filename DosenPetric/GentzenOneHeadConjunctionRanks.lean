module

public import DosenPetric.GentzenOneHeadConjunction
public import DosenPetric.GentzenOneConjunctionRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W6.OneHeadConjunction
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L Γ Θ : List (NormalForm P)}
section First
variable (p : ContractionSelection (.conj A B) F K) (f : G P Γ (A::F)) (g : G P Θ (B::U))

theorem old_rankFirst : (oldFirst p f g).rho .right (p.keep.before U)=
    (p.selected.map (fun a => f.rho .right (.there a))).sum+p.arity+2 := by
  have hn : 2≤(ContractionSelection.more (p.extend U)).arity := by
    change 2≤(p.extend U).arity+1
    rw [p.extend_arity]
    have hp:=p.arity_pos; omega
  let R : At (K++U) (.conj A B)→Nat := fun a => (oldFirst p f g).rho .right a
  let r : At (.conj A B::(F++U)) (.conj A B)→Nat := fun a => (G.conjR f g).rho .right a
  have h:=(ContractionSelection.more (p.extend U)).performR_rank (Γ++Θ) (G.conjR f g)
  change R (p.extend U).keep=
    ((At.here (.conj A B) (F++U)::(p.extend U).selected.map At.there).map r).sum+
      (if 2≤(ContractionSelection.more (p.extend U)).arity then 1 else 0) at h
  rw [ite_eq_left hn,p.extend_keep,p.extend_selected] at h
  simp only [List.map_cons,List.map_map,List.sum_cons,Function.comp_def] at h
  change (oldFirst p f g).rho .right (p.keep.before U)=
    (G.conjR f g).rho .right (.here (.conj A B) (F++U))+
      (p.selected.map (fun a => (G.conjR f g).rho .right (.there (a.before U)))).sum+1 at h
  simp only [G.rho_conjR_principal,G.rho_conjR_f] at h
  rw [G.sum_map_one_add,p.selected_length] at h
  omega

theorem repair_rankFirst : (repairFirst p f g).rho .right (p.keep.before U)=
    3+((p.prependFixed [A]).performR Γ f).rho .right (.there p.keep) := by
  have hk:=(blockFirst (U:=U) p).rankR_keep (Nat.le_refl 2) _ (middleFirst p f g)
  have hs:=(blockFirst (U:=U) p).rankR_sum (Nat.le_refl 2) _ (middleFirst p f g)
  have hp : (blockFirst (U:=U) p).keep=p.keep.before U := by
    apply At.index_injective
    rw [ContractionBlock.keep_index,At.index_before,p.keep_index]
    simp only [gaps,List.nil_append,List.append_nil]
  rw [hp] at hk
  have hsel : (blockFirst (U:=U) p).selected=[.here (.conj A B) (K++U),.there (p.keep.before U)] := by
    apply At.list_index_injective
    rw [ContractionBlock.selected_indices]
    simp only [copyOffsets,List.length_nil,List.map_cons,List.map_nil,At.index,At.index_before,
      p.keep_index,Nat.zero_add,Nat.add_comm]
  let r : At (.conj A B::(K++U)) (.conj A B)→Nat := fun a => (middleFirst p f g).rho .right a
  change (blockFirst p).rankR (Nat.le_refl 2) _ (middleFirst p f g)=1+((blockFirst p).selected.map r).sum at hs
  rw [hsel] at hs
  change (blockFirst p).rankR (Nat.le_refl 2) _ (middleFirst p f g)=
    1+(r (.here (.conj A B) (K++U))+(r (.there (p.keep.before U))+0)) at hs
  simp only [r,middleFirst,G.rho_conjR_principal,G.rho_conjR_f] at hs
  change (blockFirst p).rankR (Nat.le_refl 2) _ (middleFirst p f g)=_ at hs
  change (repairFirst p f g).rho .right (p.keep.before U)=_ at hk
  omega

theorem endpoint_leFirst : (repairFirst p f g).rho .right (p.keep.before U)≤
    (oldFirst p f g).rho .right (p.keep.before U) := by
  rw [repair_rankFirst,old_rankFirst,W6.HeadRight.premise_rank]
  have hp:=p.overhead_bound
  omega
end First
section Second
variable (q : ContractionSelection (.conj A B) U L) (f : G P Γ (A::F)) (g : G P Θ (B::U))

theorem old_rankSecond : (oldSecond q f g).rho .right (At.shift F q.keep)=
    (q.selected.map (fun a => g.rho .right (.there a))).sum+q.arity+2 := by
  have hn : 2≤(ContractionSelection.more (q.prependFixed F)).arity := by
    change 2≤(q.prependFixed F).arity+1
    rw [q.prepend_arity]
    have hp:=q.arity_pos; omega
  let R : At (F++L) (.conj A B)→Nat := fun a => (oldSecond q f g).rho .right a
  let r : At (.conj A B::(F++U)) (.conj A B)→Nat := fun a => (G.conjR f g).rho .right a
  have h:=(ContractionSelection.more (q.prependFixed F)).performR_rank (Γ++Θ) (G.conjR f g)
  change R (q.prependFixed F).keep=
    ((At.here (.conj A B) (F++U)::(q.prependFixed F).selected.map At.there).map r).sum+
      (if 2≤(ContractionSelection.more (q.prependFixed F)).arity then 1 else 0) at h
  rw [ite_eq_left hn,q.prepend_keep,q.prepend_selected] at h
  simp only [List.map_cons,List.map_map,List.sum_cons,Function.comp_def] at h
  change (oldSecond q f g).rho .right (At.shift F q.keep)=
    (G.conjR f g).rho .right (.here (.conj A B) (F++U))+
      (q.selected.map (fun a => (G.conjR f g).rho .right (.there (At.shift F a)))).sum+1 at h
  simp only [G.rho_conjR_principal,G.rho_conjR_g] at h
  rw [G.sum_map_one_add,q.selected_length] at h
  omega

theorem repair_rankSecond : (repairSecond q f g).rho .right (At.shift F q.keep)=
    3+((q.prependFixed [B]).performR Θ g).rho .right (.there q.keep) := by
  have hk:=(blockSecond (F:=F) q).rankR_keep (Nat.le_refl 2) _ (middleSecond q f g)
  have hs:=(blockSecond (F:=F) q).rankR_sum (Nat.le_refl 2) _ (middleSecond q f g)
  have hp : (blockSecond (F:=F) q).keep=At.shift F q.keep := by
    apply At.index_injective
    rw [ContractionBlock.keep_index,At.index_shift,q.keep_index]
    simp only [gaps,List.nil_append,List.append_nil,List.length_append]
  rw [hp] at hk
  have hsel : (blockSecond (F:=F) q).selected=[.here (.conj A B) (F++L),.there (At.shift F q.keep)] := by
    apply At.list_index_injective
    rw [ContractionBlock.selected_indices]
    simp only [copyOffsets,List.length_nil,List.map_cons,List.map_nil,At.index,At.index_shift,
      q.keep_index,List.length_append,Nat.zero_add,Nat.add_comm,Nat.add_left_comm]
  let r : At (.conj A B::(F++L)) (.conj A B)→Nat := fun a => (middleSecond q f g).rho .right a
  change (blockSecond q).rankR (Nat.le_refl 2) _ (middleSecond q f g)=1+((blockSecond q).selected.map r).sum at hs
  rw [hsel] at hs
  change (blockSecond q).rankR (Nat.le_refl 2) _ (middleSecond q f g)=
    1+(r (.here (.conj A B) (F++L))+(r (.there (At.shift F q.keep))+0)) at hs
  simp only [r,middleSecond,G.rho_conjR_principal,G.rho_conjR_g] at hs
  change (blockSecond q).rankR (Nat.le_refl 2) _ (middleSecond q f g)=_ at hs
  change (repairSecond q f g).rho .right (At.shift F q.keep)=_ at hk
  omega

theorem endpoint_leSecond : (repairSecond q f g).rho .right (At.shift F q.keep)≤
    (oldSecond q f g).rho .right (At.shift F q.keep) := by
  rw [repair_rankSecond,old_rankSecond,W6.HeadRight.premise_rank]
  have hp:=q.overhead_bound
  omega
end Second
end DosenPetric.Reduced.Gentzen.W6.OneHeadConjunction
