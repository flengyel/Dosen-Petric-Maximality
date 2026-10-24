module

public import DosenPetric.GentzenSelectedThinningRules

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace SelectedThinning.Data
variable (d : Data P)
theorem selected_sum (r : At d.U d.C → Nat) (s : At d.F d.C → Nat)
    (hr : ∀ a ∈ d.inner.selected, r (d.t.get a) = 1+s a) (hz : r d.z = 1) :
    (d.outer.selected.map r).sum = (d.inner.selected.map s).sum+d.gs.length+1 := by
  have he := congrArg (fun xs : List (At d.U d.C) => (xs.map r).sum) d.selected_transport
  simp only [List.map_append,List.map_map,List.map_cons,List.map_nil,List.sum_append,
    List.sum_cons,List.sum_nil,Nat.add_zero] at he
  have hm : d.inner.selected.map (fun a => r (d.t.get a)) = d.inner.selected.map (fun a => 1+s a) :=
    List.map_congr_left hr
  have hs := G.sum_map_one_add d.inner.selected s
  have hl := d.inner.selected_length
  change d.inner.selected.length = d.gs.length at hl
  change (d.outer.selected.map r).sum = (d.inner.selected.map (fun a => r (d.t.get a))).sum+r d.z at he
  have hh := congrArg List.sum hm
  have hsum := hh.trans (hs.trans
    (congrArg (fun n : Nat => (d.inner.selected.map s).sum+n) hl))
  exact he.trans ((congrArg (fun n : Nat => n+r d.z) hsum).trans
    (congrArg (fun n : Nat => (d.inner.selected.map s).sum+d.gs.length+n) hz))
end SelectedThinning.Data

namespace W2.SelectedThinning
variable (d : Gentzen.SelectedThinning.Data P) (hn : 2 ≤ d.gs.length)

section L
variable (Δ : List (NormalForm P)) (f : G P d.F Δ)
def rankNewL := d.inner.rankL hn Δ f
def rankOldL := d.outer.rankL (d.outer_bound hn) Δ (thinL d Δ f)

theorem thin_embeddedL {A : NormalForm P} (a : At d.F A) :
    (thinL d Δ f).rho .left (d.t.get a) = 1+f.rho .left a := UnaryCast.thinL_embedded ..
theorem thin_principalL : (thinL d Δ f).rho .left d.z = 1 := UnaryCast.thinL_principal ..
theorem selected_sumL :
    (d.outer.selected.map (fun a => (thinL d Δ f).rho .left a)).sum =
      (d.inner.selected.map (fun a => f.rho .left a)).sum+d.gs.length+1 :=
  d.selected_sum _ _ (fun a _ => thin_embeddedL d Δ f a) (thin_principalL d Δ f)

theorem contraction_lossL : rankOldL d hn Δ f = rankNewL d hn Δ f+d.gs.length+1 := by
  have h₀ := d.outer.rankL_sum (d.outer_bound hn) Δ (thinL d Δ f)
  have h₁ := d.inner.rankL_sum hn Δ f
  have hs := selected_sumL d Δ f
  change rankOldL d hn Δ f = _ at h₀
  change rankNewL d hn Δ f = _ at h₁
  omega
theorem old_endpointL : (oldL d hn Δ f).rho .left d.x = rankOldL d hn Δ f :=
  d.outer.rankL_keep (d.outer_bound hn) Δ (thinL d Δ f)
theorem new_endpointL : (newL d hn Δ f).rho .left d.x = rankNewL d hn Δ f+1 := by
  have he := UnaryCast.exchangeL_embedded (gaps d.gs) [d.C] d.Θ [] d.exchangeSource
    d.exchangeTarget Δ (innerL d hn Δ f) d.inner.keep
  exact ((congrArg (fun a : At d.K d.C => (newL d hn Δ f).rho .left a) d.retained).symm.trans he).trans
    ((congrArg (fun n : Nat => 1+n) (d.inner.rankL_keep hn Δ f)).trans (Nat.add_comm ..))
theorem endpoint_lossL : (oldL d hn Δ f).rho .left d.x =
    (newL d hn Δ f).rho .left d.x+d.gs.length := by
  have h₀ := old_endpointL d hn Δ f
  have h₁ := new_endpointL d hn Δ f
  have hc := contraction_lossL d hn Δ f
  omega
theorem endpoint_decreasesL : (newL d hn Δ f).rho .left d.x < (oldL d hn Δ f).rho .left d.x := by
  have he := endpoint_lossL d hn Δ f
  omega
theorem contraction_decreasesL : rankNewL d hn Δ f < rankOldL d hn Δ f := by
  have he := contraction_lossL d hn Δ f
  omega

theorem fixed_oldL {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.x.index) :
    (oldL d hn Δ f).rho .left z = 2+f.rho .left (d.original z hz) := by
  have h₀ := d.outer.rankL_fixed (d.outer_bound hn) Δ (thinL d Δ f) z
    (d.t.get (d.original z hz)) hz (d.original_old z hz)
  have h₁ := thin_embeddedL d Δ f (d.original z hz)
  exact h₀.trans ((congrArg (fun n : Nat => 1+n) h₁).trans (by omega))
theorem fixed_newL {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.x.index) :
    (newL d hn Δ f).rho .left z = 2+f.rho .left (d.original z hz) := by
  have h₀ := UnaryCast.exchangeL_embedded (gaps d.gs) [d.C] d.Θ [] d.exchangeSource
    d.exchangeTarget Δ (innerL d hn Δ f) (d.back z)
  have h₁ := d.inner.rankL_fixed hn Δ f (d.back z) (d.original z hz)
    (d.back_fixed z hz) (d.inner.fixed_get _ _)
  exact ((congrArg (fun a : At d.K A => (newL d hn Δ f).rho .left a) (d.e_back z)).symm.trans h₀).trans
    ((congrArg (fun n : Nat => 1+n) h₁).trans (by omega))
theorem fixed_equalL {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.x.index) :
    (newL d hn Δ f).rho .left z = (oldL d hn Δ f).rho .left z :=
  (fixed_newL d hn Δ f z hz).trans (fixed_oldL d hn Δ f z hz).symm
end L

section R
variable (Γ : List (NormalForm P)) (f : G P Γ d.F)
def rankNewR := d.inner.rankR hn Γ f
def rankOldR := d.outer.rankR (d.outer_bound hn) Γ (thinR d Γ f)

theorem thin_embeddedR {A : NormalForm P} (a : At d.F A) :
    (thinR d Γ f).rho .right (d.t.get a) = 1+f.rho .right a := UnaryCast.thinR_embedded ..
theorem thin_principalR : (thinR d Γ f).rho .right d.z = 1 := UnaryCast.thinR_principal ..
theorem selected_sumR :
    (d.outer.selected.map (fun a => (thinR d Γ f).rho .right a)).sum =
      (d.inner.selected.map (fun a => f.rho .right a)).sum+d.gs.length+1 :=
  d.selected_sum _ _ (fun a _ => thin_embeddedR d Γ f a) (thin_principalR d Γ f)

theorem contraction_lossR : rankOldR d hn Γ f = rankNewR d hn Γ f+d.gs.length+1 := by
  have h₀ := d.outer.rankR_sum (d.outer_bound hn) Γ (thinR d Γ f)
  have h₁ := d.inner.rankR_sum hn Γ f
  have hs := selected_sumR d Γ f
  change rankOldR d hn Γ f = _ at h₀
  change rankNewR d hn Γ f = _ at h₁
  omega
theorem old_endpointR : (oldR d hn Γ f).rho .right d.x = rankOldR d hn Γ f :=
  d.outer.rankR_keep (d.outer_bound hn) Γ (thinR d Γ f)
theorem new_endpointR : (newR d hn Γ f).rho .right d.x = rankNewR d hn Γ f+1 := by
  have he := UnaryCast.exchangeR_embedded (gaps d.gs) [d.C] d.Θ [] d.exchangeSource
    d.exchangeTarget Γ (innerR d hn Γ f) d.inner.keep
  exact ((congrArg (fun a : At d.K d.C => (newR d hn Γ f).rho .right a) d.retained).symm.trans he).trans
    ((congrArg (fun n : Nat => 1+n) (d.inner.rankR_keep hn Γ f)).trans (Nat.add_comm ..))
theorem endpoint_lossR : (oldR d hn Γ f).rho .right d.x =
    (newR d hn Γ f).rho .right d.x+d.gs.length := by
  have h₀ := old_endpointR d hn Γ f
  have h₁ := new_endpointR d hn Γ f
  have hc := contraction_lossR d hn Γ f
  omega
theorem endpoint_decreasesR : (newR d hn Γ f).rho .right d.x < (oldR d hn Γ f).rho .right d.x := by
  have he := endpoint_lossR d hn Γ f
  omega
theorem contraction_decreasesR : rankNewR d hn Γ f < rankOldR d hn Γ f := by
  have he := contraction_lossR d hn Γ f
  omega

theorem fixed_oldR {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.x.index) :
    (oldR d hn Γ f).rho .right z = 2+f.rho .right (d.original z hz) := by
  have h₀ := d.outer.rankR_fixed (d.outer_bound hn) Γ (thinR d Γ f) z
    (d.t.get (d.original z hz)) hz (d.original_old z hz)
  have h₁ := thin_embeddedR d Γ f (d.original z hz)
  exact h₀.trans ((congrArg (fun n : Nat => 1+n) h₁).trans (by omega))
theorem fixed_newR {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.x.index) :
    (newR d hn Γ f).rho .right z = 2+f.rho .right (d.original z hz) := by
  have h₀ := UnaryCast.exchangeR_embedded (gaps d.gs) [d.C] d.Θ [] d.exchangeSource
    d.exchangeTarget Γ (innerR d hn Γ f) (d.back z)
  have h₁ := d.inner.rankR_fixed hn Γ f (d.back z) (d.original z hz)
    (d.back_fixed z hz) (d.inner.fixed_get _ _)
  exact ((congrArg (fun a : At d.K A => (newR d hn Γ f).rho .right a) (d.e_back z)).symm.trans h₀).trans
    ((congrArg (fun n : Nat => 1+n) h₁).trans (by omega))
theorem fixed_equalR {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.x.index) :
    (newR d hn Γ f).rho .right z = (oldR d hn Γ f).rho .right z :=
  (fixed_newR d hn Γ f z hz).trans (fixed_oldR d hn Γ f z hz).symm
end R

end W2.SelectedThinning
end DosenPetric.Reduced.Gentzen
