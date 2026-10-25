module

public import DosenPetric.GentzenOneDisjunctionAntecedent
public import DosenPetric.GentzenNativeLogicalRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.OneDisjunctionAntecedent
universe u
variable {P : Type u} {A B C : NormalForm P} {F K U L Γ Θ : List (NormalForm P)}
section First
variable (p : ContractionSelection C F K) (f : G P (A::F) Γ) (g : G P (B::U) Θ)

theorem old_rankFirst : (oldFirst p f g).rho .left (.there (p.keep.before U))=
    (p.selected.map (fun a => f.rho .left (.there a))).sum+p.arity+(if 2≤p.arity then 1 else 0) := by
  let R : At (.disj A B::(K++U)) C→Nat := fun a => (oldFirst p f g).rho .left a
  let r : At (.disj A B::(F++U)) C→Nat := fun a => (G.disjL f g).rho .left a
  have h:=(ContractionSelection.fixed (.disj A B) (p.extend U)).performL_rank (Γ++Θ) (G.disjL f g)
  change R (.there (p.extend U).keep)=
    (((p.extend U).selected.map At.there).map r).sum+(if 2≤(p.extend U).arity then 1 else 0) at h
  rw [p.extend_keep,p.extend_selected,p.extend_arity] at h
  simp only [List.map_map,Function.comp_def] at h
  change (oldFirst p f g).rho .left (.there (p.keep.before U))=
    (p.selected.map (fun a => (G.disjL f g).rho .left (.there (a.before U)))).sum+
      (if 2≤p.arity then 1 else 0) at h
  simp only [G.rho_disjL_f] at h
  rw [G.sum_map_one_add,p.selected_length] at h
  omega

theorem repair_rankFirst : (repairFirst p f g).rho .left (.there (p.keep.before U))=
    1+(p.selected.map (fun a => f.rho .left (.there a))).sum+(if 2≤p.arity then 1 else 0) := by
  have h:=G.rho_disjL_f ((p.prependFixed [A]).performL Γ f) g p.keep
  have hp:=W6.NativeLeft.premise_rank p A f
  have hc:=congrArg (fun n => 1+n) hp
  change (repairFirst p f g).rho .left (.there (p.keep.before U))=_ at h
  omega

theorem endpoint_ltFirst (hn : 2≤p.arity) :
    (repairFirst p f g).rho .left (.there (p.keep.before U))<
      (oldFirst p f g).rho .left (.there (p.keep.before U)) := by
  rw [repair_rankFirst,old_rankFirst]
  omega
end First
section Second
variable (q : ContractionSelection C U L) (f : G P (A::F) Γ) (g : G P (B::U) Θ)

theorem old_rankSecond : (oldSecond q f g).rho .left (.there (At.shift F q.keep))=
    (q.selected.map (fun a => g.rho .left (.there a))).sum+q.arity+(if 2≤q.arity then 1 else 0) := by
  let R : At (.disj A B::(F++L)) C→Nat := fun a => (oldSecond q f g).rho .left a
  let r : At (.disj A B::(F++U)) C→Nat := fun a => (G.disjL f g).rho .left a
  have h:=(ContractionSelection.fixed (.disj A B) (q.prependFixed F)).performL_rank (Γ++Θ) (G.disjL f g)
  change R (.there (q.prependFixed F).keep)=
    (((q.prependFixed F).selected.map At.there).map r).sum+(if 2≤(q.prependFixed F).arity then 1 else 0) at h
  rw [q.prepend_keep,q.prepend_selected,q.prepend_arity] at h
  simp only [List.map_map,Function.comp_def] at h
  change (oldSecond q f g).rho .left (.there (At.shift F q.keep))=
    (q.selected.map (fun a => (G.disjL f g).rho .left (.there (At.shift F a)))).sum+
      (if 2≤q.arity then 1 else 0) at h
  simp only [G.rho_disjL_g] at h
  rw [G.sum_map_one_add,q.selected_length] at h
  omega

theorem repair_rankSecond : (repairSecond q f g).rho .left (.there (At.shift F q.keep))=
    1+(q.selected.map (fun a => g.rho .left (.there a))).sum+(if 2≤q.arity then 1 else 0) := by
  have h:=G.rho_disjL_g f ((q.prependFixed [B]).performL Θ g) q.keep
  have hp:=W6.NativeLeft.premise_rank q B g
  have hc:=congrArg (fun n => 1+n) hp
  change (repairSecond q f g).rho .left (.there (At.shift F q.keep))=_ at h
  omega

theorem endpoint_ltSecond (hn : 2≤q.arity) :
    (repairSecond q f g).rho .left (.there (At.shift F q.keep))<
      (oldSecond q f g).rho .left (.there (At.shift F q.keep)) := by
  rw [repair_rankSecond,old_rankSecond]
  omega
end Second
end DosenPetric.Reduced.Gentzen.W5.OneDisjunctionAntecedent
