module

public import DosenPetric.GentzenNonemptyRightBounds
public import DosenPetric.GentzenSelectedLogicalRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W4.NonemptyRight
universe u
variable {P : Type u} (d : Gentzen.SelectedLogical.Data P .disj)
variable (hn : 1 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ d.F)

def overhead : Nat := if 2 ≤ d.gs.length then 1 else 0
theorem overhead_le : overhead d ≤ 1 := by unfold overhead; split <;> omega

theorem inner_rank : innerRank d hn Γ f =
    (d.inner.selected.map (fun a => f.rho .right a)).sum+overhead d := by
  have h := (selection d hn).performR_rank Γ f
  rw [selection_keep,selection_selected,selection_arity] at h
  exact h

theorem old_rank : (old d hn Γ f).rho .right d.x =
    (d.inner.selected.map (fun a => f.rho .right a)).sum+d.gs.length+2 := by
  have hk := d.outer.rankR_keep (outerArity d hn) Γ (W4.SelectedLogical.logicalR d Γ f)
  have hs := d.outer.rankR_sum (outerArity d hn) Γ (W4.SelectedLogical.logicalR d Γ f)
  have hr := W4.SelectedLogical.selected_sumR d Γ f
  rw [hr] at hs
  change (old d hn Γ f).rho .right d.x = _ at hk
  omega

theorem old_balance : (old d hn Γ f).rho .right d.x+overhead d =
    innerRank d hn Γ f+d.gs.length+2 := by
  rw [old_rank,inner_rank]
  omega

theorem singleton_old_rank (he : d.gs.length=1) :
    (old d hn Γ f).rho .right d.x = innerRank d hn Γ f+3 := by
  have h:=old_balance d hn Γ f
  have ho : overhead d=0 := by simp only [overhead,he]; decide
  rw [he,ho] at h
  omega

theorem inner_lt_old : innerRank d hn Γ f < (old d hn Γ f).rho .right d.x := by
  have h:=old_balance d hn Γ f
  have ho:=overhead_le d
  omega

end DosenPetric.Reduced.Gentzen.W4.NonemptyRight
