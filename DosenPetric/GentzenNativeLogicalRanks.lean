module

public import DosenPetric.GentzenNativeLogicalRepair
public import DosenPetric.GentzenSelectionRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.G
universe u
variable {P : Type u}
theorem rho_disjL_principal {F U Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::F) Δ) (g : G P (B::U) Λ) :
    (disjL f g).rho .left (.here (.disj A B) (F++U))=1 := rho_leaf _ .left _ (by rfl)
end DosenPetric.Reduced.Gentzen.G

namespace DosenPetric.Reduced.Gentzen.W6.NativeLeft
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
variable (p : ContractionSelection (.disj A B) F K) (q : ContractionSelection (.disj A B) U L)
variable (f : G P (A::F) Δ) (g : G P (B::U) Λ)
def premiseSum : Nat := (p.selected.map (fun a => f.rho .left (.there a))).sum+
  (q.selected.map (fun a => g.rho .left (.there a))).sum
theorem old_rank : (old p q f g).rho .left (p.chain q).keep=
    premiseSum p q f g+p.arity+q.arity+2 := by
  have hn : 2≤(ContractionSelection.more (p.chain q)).arity := by
    change 2≤(p.chain q).arity+1
    rw [ContractionSelection.chain_count]
    have hp:=p.arity_pos; have hq:=q.arity_pos; omega
  let R : At (p.erased++L) (.disj A B)→Nat := fun a => (old p q f g).rho .left a
  let r : At (.disj A B::(F++U)) (.disj A B)→Nat := fun a => (G.disjL f g).rho .left a
  have h:=(ContractionSelection.more (p.chain q)).performL_rank (Δ++Λ) (G.disjL f g)
  change R (p.chain q).keep=((ContractionSelection.more (p.chain q)).selected.map r).sum+
    (if 2≤(ContractionSelection.more (p.chain q)).arity then 1 else 0) at h
  rw [ite_eq_left hn] at h
  change R (p.chain q).keep=((At.here (.disj A B) (F++U)::(p.chain q).selected.map At.there).map r).sum+1 at h
  rw [ContractionSelection.chain_selected] at h
  simp only [List.map_cons,List.map_map,List.map_append,List.sum_cons,List.sum_append,Function.comp_def] at h
  change (old p q f g).rho .left (p.chain q).keep=
    (G.disjL f g).rho .left (.here (.disj A B) (F++U))+
      ((p.selected.map (fun a => (G.disjL f g).rho .left (.there (a.before U)))).sum+
      (q.selected.map (fun a => (G.disjL f g).rho .left (.there (At.shift F a)))).sum)+1 at h
  simp only [G.rho_disjL_principal,G.rho_disjL_f,G.rho_disjL_g] at h
  rw [G.sum_map_one_add,G.sum_map_one_add,p.selected_length,q.selected_length] at h
  unfold premiseSum
  omega

theorem premise_rank {C : NormalForm P} {F K Δ : List (NormalForm P)}
    (p : ContractionSelection C F K) (A : NormalForm P) (f : G P (A::F) Δ) :
    ((p.prependFixed [A]).performL Δ f).rho .left (.there p.keep)=
      (p.selected.map (fun a => f.rho .left (.there a))).sum+(if 2≤p.arity then 1 else 0) := by
  let R : At (A::K) C→Nat := fun a => ((p.prependFixed [A]).performL Δ f).rho .left a
  let r : At (A::F) C→Nat := fun a => f.rho .left a
  have h:=(p.prependFixed [A]).performL_rank Δ f
  change R (p.prependFixed [A]).keep=((p.prependFixed [A]).selected.map r).sum+
    (if 2≤(p.prependFixed [A]).arity then 1 else 0) at h
  rw [p.prepend_keep,p.prepend_selected,p.prepend_arity] at h
  simpa only [List.map_map,Function.comp_def,At.shift,List.nil_append,R,r] using h

theorem innerF_lt : (innerF p f).rho .left (.there p.keep)<(old p q f g).rho .left (p.chain q).keep := by
  rw [old_rank]
  change ((p.prependFixed [A]).performL Δ f).rho .left (.there p.keep)<_
  rw [premise_rank]
  have hp:=p.overhead_bound
  have hq:=q.arity_pos
  unfold premiseSum
  omega

theorem innerG_lt : (innerG q g).rho .left (.there q.keep)<(old p q f g).rho .left (p.chain q).keep := by
  rw [old_rank]
  change ((q.prependFixed [B]).performL Λ g).rho .left (.there q.keep)<_
  rw [premise_rank]
  have hp:=p.arity_pos
  have hq:=q.overhead_bound
  unfold premiseSum
  omega
end DosenPetric.Reduced.Gentzen.W6.NativeLeft
