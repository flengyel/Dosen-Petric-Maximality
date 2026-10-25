module

public import DosenPetric.GentzenSelectionContraction
public import DosenPetric.GentzenMixRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionSelection
universe u
variable {P : Type u} {C : NormalForm P} {F K : List (NormalForm P)}

theorem singleton_selected (p : ContractionSelection C F F) (h : p.arity=1) :
    p.selected = [p.keep] := by
  apply At.ordered_ext _ _ p.selected_ordered (.cons (fun _ hh => by cases hh) .nil)
  intro a
  rw [List.mem_singleton,p.selected_iff,p.singleton_get h]
  rfl

theorem performL_rank (p : ContractionSelection C F K) (Δ : List (NormalForm P))
    (f : G P F Δ) :
    (p.performL Δ f).rho .left p.keep =
      (p.selected.map (fun a => f.rho .left a)).sum + (if 2 ≤ p.arity then 1 else 0) := by
  unfold performL
  split
  · rename_i hn
    have hk := p.block.rankL_keep (by rw [p.count]; exact hn) Δ f
    have hs := p.block.rankL_sum (by rw [p.count]; exact hn) Δ f
    rw [←p.keep_eq] at hk
    rw [←p.selected_eq] at hs
    exact hk.trans (hs.trans (Nat.add_comm 1 _))
  · rename_i hn
    have hs : p.arity=1 := by have hp:=p.arity_pos; omega
    cases p.singleton_endpoints hs
    rw [p.singleton_selected hs]
    rfl

theorem performR_rank (p : ContractionSelection C F K) (Γ : List (NormalForm P))
    (f : G P Γ F) :
    (p.performR Γ f).rho .right p.keep =
      (p.selected.map (fun a => f.rho .right a)).sum + (if 2 ≤ p.arity then 1 else 0) := by
  unfold performR
  split
  · rename_i hn
    have hk := p.block.rankR_keep (by rw [p.count]; exact hn) Γ f
    have hs := p.block.rankR_sum (by rw [p.count]; exact hn) Γ f
    rw [←p.keep_eq] at hk
    rw [←p.selected_eq] at hs
    exact hk.trans (hs.trans (Nat.add_comm 1 _))
  · rename_i hn
    have hs : p.arity=1 := by have hp:=p.arity_pos; omega
    cases p.singleton_endpoints hs
    rw [p.singleton_selected hs]
    rfl

theorem overhead_bound (p : ContractionSelection C F K) :
    (if 2 ≤ p.arity then 1 else 0)+1 ≤ p.arity := by
  have hp:=p.arity_pos
  split <;> omega

end DosenPetric.Reduced.Gentzen.ContractionSelection
