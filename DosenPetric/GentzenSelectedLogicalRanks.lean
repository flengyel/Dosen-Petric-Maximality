module

public import DosenPetric.GentzenSelectedLogicalRules
public import DosenPetric.GentzenSelectedLogicalFibers
public import DosenPetric.GentzenSelectedThinningRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace SelectedLogical.Data
variable {o : Op} (d : Data P o)
theorem selected_sum (r : At d.U d.C → Nat) (s : At d.F d.C → Nat)
    (hr : ∀ a ∈ d.s.inner.selected, r (a.before [d.C]) = 1+s (a.before [d.A,d.B]))
    (hz : r d.s.z = 1) :
    (d.outer.selected.map r).sum = (d.inner.selected.map s).sum+d.gs.length+1 := by
  have he := d.s.selected_sum r (fun a => s (a.before [d.A,d.B]))
    (fun a ha => (congrArg r (d.t_before a)).trans (hr a ha)) hz
  have hi : (d.inner.selected.map s).sum =
      (d.s.inner.selected.map (fun a => s (a.before [d.A,d.B]))).sum := by
    rw [d.inner_selected,List.map_map]
    rfl
  exact he.trans (congrArg (fun n => n+d.gs.length+1) hi.symm)
theorem retained_parent : d.iParent d.inner.keep = some d.k := by
  rw [ContractionBlock.extend_keep]
  exact d.i_prefix d.s.inner.keep
end SelectedLogical.Data

namespace W4.SelectedLogical

section L
variable (d : Gentzen.SelectedLogical.Data P .conj) (hn : 2 ≤ d.gs.length)
variable (Δ : List (NormalForm P)) (f : G P d.F Δ)
def rankInnerL := d.inner.rankL hn Δ f
def rankOuterL := d.outer.rankL (d.s.outer_bound hn) Δ (logicalL d Δ f)

theorem logical_embeddedL {E : NormalForm P} (a : At d.s.F E) :
    (logicalL d Δ f).rho .left (a.before [d.C]) =
      1+f.rho .left (a.before [d.A,d.B]) :=
  G.rho_conjL_surviving d.s.F [] Δ d.A d.B f _ _ (d.u_prefix a)
theorem logical_principalL : (logicalL d Δ f).rho .left d.s.z = 1 :=
  G.rho_conjL_principal d.s.F [] Δ d.A d.B f
theorem selected_sumL :
    (d.outer.selected.map (fun a => (logicalL d Δ f).rho .left a)).sum =
      (d.inner.selected.map (fun a => f.rho .left a)).sum+d.gs.length+1 :=
  d.selected_sum _ _ (fun a _ => logical_embeddedL d Δ f a) (logical_principalL d Δ f)
theorem contraction_lossL : rankOuterL d hn Δ f =
    rankInnerL d hn Δ f+d.gs.length+1 := by
  have h₀ := d.outer.rankL_sum (d.s.outer_bound hn) Δ (logicalL d Δ f)
  have h₁ := d.inner.rankL_sum hn Δ f
  have hs := selected_sumL d Δ f
  change rankOuterL d hn Δ f = _ at h₀
  change rankInnerL d hn Δ f = _ at h₁
  omega
theorem contraction_decreasesL : rankInnerL d hn Δ f < rankOuterL d hn Δ f := by
  have h := contraction_lossL d hn Δ f
  omega
theorem old_endpointL : (oldL d hn Δ f).rho .left d.x =
    rankInnerL d hn Δ f+d.gs.length+1 :=
  (d.outer.rankL_keep (d.s.outer_bound hn) Δ (logicalL d Δ f)).trans (contraction_lossL d hn Δ f)

theorem middle_retainedL : (middleL d hn Δ f).rho .left d.k =
    1+rankInnerL d hn Δ f := by
  have h := G.rho_conjL_surviving d.s.I [] Δ d.A d.B (innerL d hn Δ f) _ _ d.retained_parent
  exact h.trans (congrArg (fun n => 1+n) (d.inner.rankL_keep hn Δ f))
theorem middle_principalL : (middleL d hn Δ f).rho .left d.q = 1 :=
  G.rho_conjL_principal d.s.I [] Δ d.A d.B (innerL d hn Δ f)
theorem new_endpointL : (newL d hn Δ f).rho .left d.x =
    rankInnerL d hn Δ f+3 := by
  have hk := d.last.rankL_keep (Nat.le_refl 2) Δ (middleL d hn Δ f)
  have hs := d.last.rankL_sum (Nat.le_refl 2) Δ (middleL d hn Δ f)
  rw [d.last_keep] at hk
  rw [d.last_selected] at hs
  have hr := middle_retainedL d hn Δ f
  have hp := middle_principalL d hn Δ f
  change _ = 1+((middleL d hn Δ f).rho .left d.k+
    ((middleL d hn Δ f).rho .left d.q+0)) at hs
  rw [hr,hp] at hs
  change (newL d hn Δ f).rho .left d.x = _ at hk
  omega
theorem endpoint_balanceL : (oldL d hn Δ f).rho .left d.x+2 =
    (newL d hn Δ f).rho .left d.x+d.gs.length := by
  have ho := old_endpointL d hn Δ f
  have he := new_endpointL d hn Δ f
  omega
theorem endpoint_leL : (newL d hn Δ f).rho .left d.x ≤
    (oldL d hn Δ f).rho .left d.x := by
  have h := endpoint_balanceL d hn Δ f
  omega
theorem endpoint_tieL (he : d.gs.length = 2) :
    (newL d hn Δ f).rho .left d.x = (oldL d hn Δ f).rho .left d.x := by
  have h := endpoint_balanceL d hn Δ f
  omega
theorem endpoint_decreasesL (he : 3 ≤ d.gs.length) :
    (newL d hn Δ f).rho .left d.x < (oldL d hn Δ f).rho .left d.x := by
  have h := endpoint_balanceL d hn Δ f
  omega

theorem fixed_oldL {E : NormalForm P} (z : At d.K E) (hz : z.index ≠ d.x.index) :
    (oldL d hn Δ f).rho .left z = 2+f.rho .left (d.original z hz) := by
  have h₀ := d.outer.rankL_fixed (d.s.outer_bound hn) Δ (logicalL d Δ f)
    z (d.oldFixed z hz) hz (d.original_old z hz)
  have h₁ := G.rho_conjL_surviving d.s.F [] Δ d.A d.B f _ _ (d.original_parent z hz)
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem fixed_newL {E : NormalForm P} (z : At d.K E) (hz : z.index ≠ d.x.index) :
    (newL d hn Δ f).rho .left z = 3+f.rho .left (d.original z hz) := by
  have h₀ := d.last.rankL_fixed (Nat.le_refl 2) Δ (middleL d hn Δ f)
    z (d.newFixed z) (by rw [d.last_keep]; exact hz) (d.original_last z)
  have h₁ := G.rho_conjL_surviving d.s.I [] Δ d.A d.B (innerL d hn Δ f) _ _ (d.fixed_parent z)
  have h₂ := d.inner.rankL_fixed hn Δ f (d.innerFixed z) (d.original z hz)
    (d.inner_fixed z hz) (d.original_inner z hz)
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans
    ((congrArg (fun n => 1+(1+n)) h₂).trans (by omega)))
theorem fixed_increasesL {E : NormalForm P} (z : At d.K E) (hz : z.index ≠ d.x.index) :
    (newL d hn Δ f).rho .left z = (oldL d hn Δ f).rho .left z+1 := by
  have ho := fixed_oldL d hn Δ f z hz
  have he := fixed_newL d hn Δ f z hz
  omega
end L

section R
variable (d : Gentzen.SelectedLogical.Data P .disj) (hn : 2 ≤ d.gs.length)
variable (Γ : List (NormalForm P)) (f : G P Γ d.F)
def rankInnerR := d.inner.rankR hn Γ f
def rankOuterR := d.outer.rankR (d.s.outer_bound hn) Γ (logicalR d Γ f)

theorem logical_embeddedR {E : NormalForm P} (a : At d.s.F E) :
    (logicalR d Γ f).rho .right (a.before [d.C]) =
      1+f.rho .right (a.before [d.A,d.B]) :=
  G.rho_disjR_surviving Γ d.s.F [] d.A d.B f _ _ (d.u_prefix a)
theorem logical_principalR : (logicalR d Γ f).rho .right d.s.z = 1 :=
  G.rho_disjR_principal Γ d.s.F [] d.A d.B f
theorem selected_sumR :
    (d.outer.selected.map (fun a => (logicalR d Γ f).rho .right a)).sum =
      (d.inner.selected.map (fun a => f.rho .right a)).sum+d.gs.length+1 :=
  d.selected_sum _ _ (fun a _ => logical_embeddedR d Γ f a) (logical_principalR d Γ f)
theorem contraction_lossR : rankOuterR d hn Γ f =
    rankInnerR d hn Γ f+d.gs.length+1 := by
  have h₀ := d.outer.rankR_sum (d.s.outer_bound hn) Γ (logicalR d Γ f)
  have h₁ := d.inner.rankR_sum hn Γ f
  have hs := selected_sumR d Γ f
  change rankOuterR d hn Γ f = _ at h₀
  change rankInnerR d hn Γ f = _ at h₁
  omega
theorem contraction_decreasesR : rankInnerR d hn Γ f < rankOuterR d hn Γ f := by
  have h := contraction_lossR d hn Γ f
  omega
theorem old_endpointR : (oldR d hn Γ f).rho .right d.x =
    rankInnerR d hn Γ f+d.gs.length+1 :=
  (d.outer.rankR_keep (d.s.outer_bound hn) Γ (logicalR d Γ f)).trans (contraction_lossR d hn Γ f)

theorem middle_retainedR : (middleR d hn Γ f).rho .right d.k =
    1+rankInnerR d hn Γ f := by
  have h := G.rho_disjR_surviving Γ d.s.I [] d.A d.B (innerR d hn Γ f) _ _ d.retained_parent
  exact h.trans (congrArg (fun n => 1+n) (d.inner.rankR_keep hn Γ f))
theorem middle_principalR : (middleR d hn Γ f).rho .right d.q = 1 :=
  G.rho_disjR_principal Γ d.s.I [] d.A d.B (innerR d hn Γ f)
theorem new_endpointR : (newR d hn Γ f).rho .right d.x =
    rankInnerR d hn Γ f+3 := by
  have hk := d.last.rankR_keep (Nat.le_refl 2) Γ (middleR d hn Γ f)
  have hs := d.last.rankR_sum (Nat.le_refl 2) Γ (middleR d hn Γ f)
  rw [d.last_keep] at hk
  rw [d.last_selected] at hs
  have hr := middle_retainedR d hn Γ f
  have hp := middle_principalR d hn Γ f
  change _ = 1+((middleR d hn Γ f).rho .right d.k+
    ((middleR d hn Γ f).rho .right d.q+0)) at hs
  rw [hr,hp] at hs
  change (newR d hn Γ f).rho .right d.x = _ at hk
  omega
theorem endpoint_balanceR : (oldR d hn Γ f).rho .right d.x+2 =
    (newR d hn Γ f).rho .right d.x+d.gs.length := by
  have ho := old_endpointR d hn Γ f
  have he := new_endpointR d hn Γ f
  omega
theorem endpoint_leR : (newR d hn Γ f).rho .right d.x ≤
    (oldR d hn Γ f).rho .right d.x := by
  have h := endpoint_balanceR d hn Γ f
  omega
theorem endpoint_tieR (he : d.gs.length = 2) :
    (newR d hn Γ f).rho .right d.x = (oldR d hn Γ f).rho .right d.x := by
  have h := endpoint_balanceR d hn Γ f
  omega
theorem endpoint_decreasesR (he : 3 ≤ d.gs.length) :
    (newR d hn Γ f).rho .right d.x < (oldR d hn Γ f).rho .right d.x := by
  have h := endpoint_balanceR d hn Γ f
  omega

theorem fixed_oldR {E : NormalForm P} (z : At d.K E) (hz : z.index ≠ d.x.index) :
    (oldR d hn Γ f).rho .right z = 2+f.rho .right (d.original z hz) := by
  have h₀ := d.outer.rankR_fixed (d.s.outer_bound hn) Γ (logicalR d Γ f)
    z (d.oldFixed z hz) hz (d.original_old z hz)
  have h₁ := G.rho_disjR_surviving Γ d.s.F [] d.A d.B f _ _ (d.original_parent z hz)
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem fixed_newR {E : NormalForm P} (z : At d.K E) (hz : z.index ≠ d.x.index) :
    (newR d hn Γ f).rho .right z = 3+f.rho .right (d.original z hz) := by
  have h₀ := d.last.rankR_fixed (Nat.le_refl 2) Γ (middleR d hn Γ f)
    z (d.newFixed z) (by rw [d.last_keep]; exact hz) (d.original_last z)
  have h₁ := G.rho_disjR_surviving Γ d.s.I [] d.A d.B (innerR d hn Γ f) _ _ (d.fixed_parent z)
  have h₂ := d.inner.rankR_fixed hn Γ f (d.innerFixed z) (d.original z hz)
    (d.inner_fixed z hz) (d.original_inner z hz)
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans
    ((congrArg (fun n => 1+(1+n)) h₂).trans (by omega)))
theorem fixed_increasesR {E : NormalForm P} (z : At d.K E) (hz : z.index ≠ d.x.index) :
    (newR d hn Γ f).rho .right z = (oldR d hn Γ f).rho .right z+1 := by
  have ho := fixed_oldR d hn Γ f z hz
  have he := fixed_newR d hn Γ f z hz
  omega
end R

end W4.SelectedLogical
end DosenPetric.Reduced.Gentzen
