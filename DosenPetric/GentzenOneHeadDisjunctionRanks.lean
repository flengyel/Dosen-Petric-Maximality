module

public import DosenPetric.GentzenOneHeadDisjunction

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W6.OneHeadDisjunction
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
section First
variable (p : ContractionSelection (.disj A B) F K) (f : G P (A::F) Δ) (g : G P (B::U) Λ)
theorem old_rankFirst : (oldFirst p f g).rho .left (p.keep.before U)=
    (p.selected.map (fun a => f.rho .left (.there a))).sum+p.arity+2 := by
  have hn : 2≤(ContractionSelection.more (p.extend U)).arity := by
    change 2≤(p.extend U).arity+1
    rw [p.extend_arity]
    have hp:=p.arity_pos; omega
  let R : At (K++U) (.disj A B)→Nat := fun a => (oldFirst p f g).rho .left a
  let r : At (.disj A B::(F++U)) (.disj A B)→Nat := fun a => (G.disjL f g).rho .left a
  have h:=(ContractionSelection.more (p.extend U)).performL_rank (Δ++Λ) (G.disjL f g)
  change R (p.extend U).keep=
    ((At.here (.disj A B) (F++U)::(p.extend U).selected.map At.there).map r).sum+
      (if 2≤(ContractionSelection.more (p.extend U)).arity then 1 else 0) at h
  rw [ite_eq_left hn,p.extend_keep,p.extend_selected] at h
  simp only [List.map_cons,List.map_map,List.sum_cons,Function.comp_def] at h
  change (oldFirst p f g).rho .left (p.keep.before U)=
    (G.disjL f g).rho .left (.here (.disj A B) (F++U))+
      (p.selected.map (fun a => (G.disjL f g).rho .left (.there (a.before U)))).sum+1 at h
  simp only [G.rho_disjL_principal,G.rho_disjL_f] at h
  rw [G.sum_map_one_add,p.selected_length] at h
  omega


def limitFirst : Nat := (oldFirst p f g).rho .left (p.keep.before U)
theorem inner_ltFirst : (innerFirst p f).rho .left (.there p.keep)<limitFirst p f g := by
  change ((p.prependFixed [A]).performL _ f).rho .left (.there p.keep)<(oldFirst p f g).rho .left (p.keep.before U)
  rw [NativeLeft.premise_rank,old_rankFirst]
  have hp:=p.overhead_bound; omega
end First
section Second
variable (q : ContractionSelection (.disj A B) U L) (f : G P (A::F) Δ) (g : G P (B::U) Λ)
theorem old_rankSecond : (oldSecond q f g).rho .left (At.shift F q.keep)=
    (q.selected.map (fun a => g.rho .left (.there a))).sum+q.arity+2 := by
  have hn : 2≤(ContractionSelection.more (q.prependFixed F)).arity := by
    change 2≤(q.prependFixed F).arity+1
    rw [q.prepend_arity]
    have hp:=q.arity_pos; omega
  let R : At (F++L) (.disj A B)→Nat := fun a => (oldSecond q f g).rho .left a
  let r : At (.disj A B::(F++U)) (.disj A B)→Nat := fun a => (G.disjL f g).rho .left a
  have h:=(ContractionSelection.more (q.prependFixed F)).performL_rank (Δ++Λ) (G.disjL f g)
  change R (q.prependFixed F).keep=
    ((At.here (.disj A B) (F++U)::(q.prependFixed F).selected.map At.there).map r).sum+
      (if 2≤(ContractionSelection.more (q.prependFixed F)).arity then 1 else 0) at h
  rw [ite_eq_left hn,q.prepend_keep,q.prepend_selected] at h
  simp only [List.map_cons,List.map_map,List.sum_cons,Function.comp_def] at h
  change (oldSecond q f g).rho .left (At.shift F q.keep)=
    (G.disjL f g).rho .left (.here (.disj A B) (F++U))+
      (q.selected.map (fun a => (G.disjL f g).rho .left (.there (At.shift F a)))).sum+1 at h
  simp only [G.rho_disjL_principal,G.rho_disjL_g] at h
  rw [G.sum_map_one_add,q.selected_length] at h
  omega


def limitSecond : Nat := (oldSecond q f g).rho .left (At.shift F q.keep)
theorem inner_ltSecond : (innerSecond q g).rho .left (.there q.keep)<limitSecond q f g := by
  change ((q.prependFixed [B]).performL _ g).rho .left (.there q.keep)<(oldSecond q f g).rho .left (At.shift F q.keep)
  rw [NativeLeft.premise_rank,old_rankSecond]
  have hq:=q.overhead_bound; omega
end Second
end DosenPetric.Reduced.Gentzen.W6.OneHeadDisjunction
