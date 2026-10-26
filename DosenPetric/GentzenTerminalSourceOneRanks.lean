module

public import DosenPetric.GentzenTerminalSourceOne

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W6.TerminalOne
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
section First
variable (p : ContractionSelection (.disj A B) F K) (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ)

theorem old_rankFirst : (oldFirst p f g).rho .left (p.extend U).lastKeep=
    (p.selected.map (fun a=>f.rho .left (a.before [A]))).sum+3*p.arity+3 := by
  let R : At ((p.extend U).erased++[.disj A B]) (.disj A B)→Nat := fun x=>(oldFirst p f g).rho .left x
  let r : At ((F++U)++[.disj A B]) (.disj A B)→Nat := fun x=>(BlockedSource.disjLLast f g).rho .left x
  have h:=((p.extend U).chain (.last [])).performL_rank (Δ++Λ) (BlockedSource.disjLLast f g)
  change R ((p.extend U).chain (.last [])).keep=
    (((p.extend U).chain (.last [])).selected.map r).sum+(if 2≤((p.extend U).chain (.last [])).arity then 1 else 0) at h
  rw [ContractionSelection.terminal_keep,ContractionSelection.terminal_selected,
    ite_eq_left (p.extend U).terminal_arity,p.extend_selected] at h
  simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,List.map_map,Function.comp_def] at h
  change (oldFirst p f g).rho .left (p.extend U).lastKeep=
    (p.selected.map (fun a=>(BlockedSource.disjLLast f g).rho .left ((a.before U).before [.disj A B]))).sum+
      (BlockedSource.disjLLast f g).rho .left (At.shift (F++U) (.here (.disj A B) []))+1 at h
  simp only [BlockedSource.disjLLast_rank_f,BlockedSource.disjLLast_rank_principal] at h
  rw [sum_map_const_add,p.selected_length] at h
  change R (p.extend U).lastKeep=3*p.arity+(p.selected.map (fun a=>f.rho .left (a.before [A]))).sum+2+1 at h
  change R (p.extend U).lastKeep=(p.selected.map (fun a=>f.rho .left (a.before [A]))).sum+3*p.arity+3
  omega

theorem repair_rankFirst : (repairFirst p f g).rho .left (p.extend U).lastKeep=
    (p.selected.map (fun a=>f.rho .left (a.before [A]))).sum+(if 2≤p.arity then 1 else 0)+6 := by
  have hk:=(p.extend U).retainedLastBlock.rankL_keep (p.extend U).retainedLast_bound _ (middleFirst p f g)
  have hs:=(p.extend U).retainedLastBlock.rankL_sum (p.extend U).retainedLast_bound _ (middleFirst p f g)
  rw [ContractionSelection.retainedLast_keep] at hk
  let r : At ((K++U)++[.disj A B]) (.disj A B)→Nat := fun x=>(middleFirst p f g).rho .left x
  change (p.extend U).retainedLastBlock.rankL (p.extend U).retainedLast_bound _ (middleFirst p f g)=
    1+((p.extend U).retainedLastBlock.selected.map r).sum at hs
  rw [ContractionSelection.retainedLast_selected,p.extend_keep] at hs
  change (p.extend U).retainedLastBlock.rankL (p.extend U).retainedLast_bound _ (middleFirst p f g)=
    1+(r ((p.keep.before U).before [.disj A B])+(r (At.shift (K++U) (.here (.disj A B) []))+0)) at hs
  simp only [r,middleFirst,BlockedSource.disjLLast_rank_f,BlockedSource.disjLLast_rank_principal] at hs
  have hi:=SourceLeft.premise_rank p A f
  change (innerFirst p f).rho .left (p.keep.before [A])=_ at hi
  change (repairFirst p f g).rho .left (p.extend U).lastKeep=_ at hk
  change (p.extend U).retainedLastBlock.rankL (p.extend U).retainedLast_bound _ (middleFirst p f g)=_ at hs
  omega

theorem endpoint_leFirst : (repairFirst p f g).rho .left (p.extend U).lastKeep≤
    (oldFirst p f g).rho .left (p.extend U).lastKeep := by
  rw [repair_rankFirst,old_rankFirst]
  have h:=p.overhead_bound
  omega
end First
section Second
variable (q : ContractionSelection (.disj A B) U L) (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ)

theorem old_rankSecond : (oldSecond q f g).rho .left (q.prependFixed F).lastKeep=
    (q.selected.map (fun a=>g.rho .left (a.before [B]))).sum+3*q.arity+3 := by
  let R : At ((q.prependFixed F).erased++[.disj A B]) (.disj A B)→Nat := fun x=>(oldSecond q f g).rho .left x
  let r : At ((F++U)++[.disj A B]) (.disj A B)→Nat := fun x=>(BlockedSource.disjLLast f g).rho .left x
  have h:=((q.prependFixed F).chain (.last [])).performL_rank (Δ++Λ) (BlockedSource.disjLLast f g)
  change R ((q.prependFixed F).chain (.last [])).keep=
    (((q.prependFixed F).chain (.last [])).selected.map r).sum+(if 2≤((q.prependFixed F).chain (.last [])).arity then 1 else 0) at h
  rw [ContractionSelection.terminal_keep,ContractionSelection.terminal_selected,
    ite_eq_left (q.prependFixed F).terminal_arity,q.prepend_selected] at h
  simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,List.map_map,Function.comp_def] at h
  change (oldSecond q f g).rho .left (q.prependFixed F).lastKeep=
    (q.selected.map (fun a=>(BlockedSource.disjLLast f g).rho .left ((At.shift F a).before [.disj A B]))).sum+
      (BlockedSource.disjLLast f g).rho .left (At.shift (F++U) (.here (.disj A B) []))+1 at h
  simp only [BlockedSource.disjLLast_rank_g,BlockedSource.disjLLast_rank_principal] at h
  rw [sum_map_const_add,q.selected_length] at h
  change R (q.prependFixed F).lastKeep=3*q.arity+(q.selected.map (fun a=>g.rho .left (a.before [B]))).sum+2+1 at h
  change R (q.prependFixed F).lastKeep=(q.selected.map (fun a=>g.rho .left (a.before [B]))).sum+3*q.arity+3
  omega

theorem repair_rankSecond : (repairSecond q f g).rho .left (q.prependFixed F).lastKeep=
    (q.selected.map (fun a=>g.rho .left (a.before [B]))).sum+(if 2≤q.arity then 1 else 0)+6 := by
  have hk:=(q.prependFixed F).retainedLastBlock.rankL_keep (q.prependFixed F).retainedLast_bound _ (middleSecond q f g)
  have hs:=(q.prependFixed F).retainedLastBlock.rankL_sum (q.prependFixed F).retainedLast_bound _ (middleSecond q f g)
  rw [ContractionSelection.retainedLast_keep] at hk
  let r : At ((F++L)++[.disj A B]) (.disj A B)→Nat := fun x=>(middleSecond q f g).rho .left x
  change (q.prependFixed F).retainedLastBlock.rankL (q.prependFixed F).retainedLast_bound _ (middleSecond q f g)=
    1+((q.prependFixed F).retainedLastBlock.selected.map r).sum at hs
  rw [ContractionSelection.retainedLast_selected,q.prepend_keep] at hs
  change (q.prependFixed F).retainedLastBlock.rankL (q.prependFixed F).retainedLast_bound _ (middleSecond q f g)=
    1+(r ((At.shift F q.keep).before [.disj A B])+(r (At.shift (F++L) (.here (.disj A B) []))+0)) at hs
  simp only [r,middleSecond,BlockedSource.disjLLast_rank_g,BlockedSource.disjLLast_rank_principal] at hs
  have hi:=SourceLeft.premise_rank q B g
  change (innerSecond q g).rho .left (q.keep.before [B])=_ at hi
  change (repairSecond q f g).rho .left (q.prependFixed F).lastKeep=_ at hk
  change (q.prependFixed F).retainedLastBlock.rankL (q.prependFixed F).retainedLast_bound _ (middleSecond q f g)=_ at hs
  omega

theorem endpoint_leSecond : (repairSecond q f g).rho .left (q.prependFixed F).lastKeep≤
    (oldSecond q f g).rho .left (q.prependFixed F).lastKeep := by
  rw [repair_rankSecond,old_rankSecond]
  have h:=q.overhead_bound
  omega
end Second
end DosenPetric.Reduced.Gentzen.W6.TerminalOne
