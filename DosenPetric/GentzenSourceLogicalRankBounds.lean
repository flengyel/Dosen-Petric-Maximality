module

public import DosenPetric.GentzenTerminalLogicalRanks
public import DosenPetric.GentzenSourceLogicalPositions
public import DosenPetric.GentzenSelectionRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem sum_map_const_add {T : Type u} (xs : List T) (r : T→Nat) (k : Nat) :
    (xs.map (fun a => k+r a)).sum=k*xs.length+(xs.map r).sum := by
  induction xs with
  | nil => simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.mul_zero,Nat.add_zero]
  | cons a xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.mul_add,Nat.mul_one]
    omega

namespace W6.SourceLeft
variable {A B : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
variable (p : ContractionSelection (.disj A B) F K) (q : ContractionSelection (.disj A B) U L)
variable (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ)

def premiseSum : Nat := (p.selected.map (fun a => f.rho .left (a.before [A]))).sum+
  (q.selected.map (fun a => g.rho .left (a.before [B]))).sum

theorem old_rank : (old p q f g).rho .left (p.sourceKeep q)=
    premiseSum p q f g+3*p.arity+3*q.arity+3 := by
  have hn : 2≤(p.sourceOld q).arity := by
    rw [ContractionSelection.sourceOld_arity]
    have hp:=p.arity_pos
    have hq:=q.arity_pos
    omega
  let R : At (p.erased++(q.erased++[.disj A B])) (.disj A B)→Nat :=
    fun x => (old p q f g).rho .left x
  let r : At ((F++U)++[.disj A B]) (.disj A B)→Nat :=
    fun x => (BlockedSource.disjLLast f g).rho .left x
  have h:=(p.sourceOld q).performL_rank (Δ++Λ) (BlockedSource.disjLLast f g)
  change R (p.sourceOld q).keep=((p.sourceOld q).selected.map r).sum+
    (if 2≤(p.sourceOld q).arity then 1 else 0) at h
  rw [ContractionSelection.sourceOld_keep,ContractionSelection.sourceOld_selected,ite_eq_left hn] at h
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,List.map_map,Function.comp_def] at h
  change (old p q f g).rho .left (p.sourceKeep q)=
    (p.selected.map (fun a => (BlockedSource.disjLLast f g).rho .left ((a.before U).before [.disj A B]))).sum+
    ((q.selected.map (fun a => (BlockedSource.disjLLast f g).rho .left ((At.shift F a).before [.disj A B]))).sum+
      (BlockedSource.disjLLast f g).rho .left (At.shift (F++U) (.here (.disj A B) [])))+1 at h
  simp only [BlockedSource.disjLLast_rank_f,BlockedSource.disjLLast_rank_g,
    BlockedSource.disjLLast_rank_principal] at h
  rw [sum_map_const_add,sum_map_const_add,p.selected_length,q.selected_length] at h
  unfold premiseSum
  omega

theorem repair_rank : (repair p q f g).rho .left (p.sourceKeep q)=
    9+((p.extend [A]).performL Δ f).rho .left (p.keep.before [A])+
      ((q.extend [B]).performL Λ g).rho .left (q.keep.before [B]) := by
  have hn : 2≤(p.sourceRetained q).arity := by rw [ContractionSelection.sourceRetained_arity]; decide
  have h:=(p.sourceRetained q).performL_rank (Δ++Λ) (middle p q f g)
  rw [ContractionSelection.sourceRetained_keep,ContractionSelection.sourceRetained_selected,ite_eq_left hn] at h
  change (repair p q f g).rho .left (p.sourceKeep q)=
    (middle p q f g).rho .left ((p.keep.before L).before [.disj A B])+
      ((middle p q f g).rho .left ((At.shift K q.keep).before [.disj A B])+
      ((middle p q f g).rho .left (At.shift (K++L) (.here (.disj A B) []))+0))+1 at h
  simp only [middle,BlockedSource.disjLLast_rank_f,BlockedSource.disjLLast_rank_g,
    BlockedSource.disjLLast_rank_principal] at h
  omega

theorem premise_rank {C : NormalForm P} {F K Δ : List (NormalForm P)}
    (p : ContractionSelection C F K) (A : NormalForm P) (f : G P (F++[A]) Δ) :
    ((p.extend [A]).performL Δ f).rho .left (p.keep.before [A])=
      (p.selected.map (fun a => f.rho .left (a.before [A]))).sum+(if 2≤p.arity then 1 else 0) := by
  have h:=(p.extend [A]).performL_rank Δ f
  change ((p.extend [A]).performL Δ f).rho .left ((p.extend [A]).keep)=
    ((p.extend [A]).selected.map (fun a : At (F++[A]) C => f.rho .left a)).sum+
      (if 2≤(p.extend [A]).arity then 1 else 0) at h
  rw [p.extend_keep,p.extend_selected,p.extend_arity] at h
  simpa only [List.map_map,Function.comp_def] using h

theorem endpoint_le : (repair p q f g).rho .left (p.sourceKeep q)≤
    (old p q f g).rho .left (p.sourceKeep q) := by
  rw [repair_rank,old_rank,premise_rank,premise_rank]
  have hp:=p.overhead_bound
  have hq:=q.overhead_bound
  unfold premiseSum
  omega

end W6.SourceLeft
end DosenPetric.Reduced.Gentzen
