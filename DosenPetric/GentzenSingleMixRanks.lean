module

public import DosenPetric.GentzenSingleMixRules
public import DosenPetric.GentzenMixRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.SinglePremiseMix
universe u
variable {P : Type u} {F K : List (NormalForm P)}
variable (d : ContractionBlock P F K) (hn : 2 ≤ d.gs.length)

section L
variable {Φ Ψ Δ : List (NormalForm P)} (f : G P Φ Ψ) (g : G P F Δ)
def rankInnerL := d.rankL hn Δ g
def rankOuterL := (d.extend Φ).rankL hn _ (G.mix f g)
theorem selected_sumL :
    ((d.extend Φ).selected.map (fun a => (G.mix f g).rho .left a)).sum =
      (d.selected.map (fun a => g.rho .left a)).sum+d.gs.length := by
  have ht := congrArg (fun xs : List (At (F++Φ) d.C) =>
    (xs.map (fun a => (G.mix f g).rho .left a)).sum) (d.extend_selected Φ)
  have hm : ((d.selected.map (fun a => a.before Φ)).map
      (fun a => (G.mix f g).rho .left a)).sum =
      (d.selected.map (fun a => 1+g.rho .left a)).sum := by
    exact congrArg List.sum ((List.map_map ..).trans (List.map_congr_left (fun a _ => G.rho_mix_g_left f g a)))
  exact ht.trans (hm.trans ((G.sum_map_one_add d.selected (fun a => g.rho .left a)).trans
    (congrArg (fun n => (d.selected.map (fun a => g.rho .left a)).sum+n) d.selected_length)))
theorem contraction_lossL : rankOuterL d hn f g = rankInnerL d hn g+d.gs.length := by
  have ho := (d.extend Φ).rankL_sum hn _ (G.mix f g)
  have hi := d.rankL_sum hn Δ g
  have hs := selected_sumL d f g
  change rankOuterL d hn f g = _ at ho
  change rankInnerL d hn g = _ at hi
  omega
theorem old_endpointL : (oldL d hn f g).rho .left (d.keep.before Φ) = rankOuterL d hn f g := by
  have h := (d.extend Φ).rankL_keep hn _ (G.mix f g)
  rw [d.extend_keep] at h
  exact h
theorem new_endpointL : (newL d hn f g).rho .left (d.keep.before Φ) = rankInnerL d hn g+1 := by
  have h := G.rho_mix_g_left f (innerL d hn g) d.keep
  exact h.trans ((congrArg (fun n => 1+n) (d.rankL_keep hn Δ g)).trans (Nat.add_comm ..))
theorem endpoint_balanceL : (oldL d hn f g).rho .left (d.keep.before Φ)+1 =
    (newL d hn f g).rho .left (d.keep.before Φ)+d.gs.length := by
  have ho := old_endpointL d hn f g
  have he := new_endpointL d hn f g
  have hl := contraction_lossL d hn f g
  omega
theorem contraction_decreasesL : rankInnerL d hn g < rankOuterL d hn f g := by
  have h := contraction_lossL d hn f g
  omega
theorem endpoint_decreasesL : (newL d hn f g).rho .left (d.keep.before Φ) < (oldL d hn f g).rho .left (d.keep.before Φ) := by
  have h := endpoint_balanceL d hn f g
  omega

theorem fixed_g_oldL {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) :
    (oldL d hn f g).rho .left (z.before Φ) = 2+g.rho .left (d.fixed z hz) := by
  have h₀ := (d.extend Φ).rankL_fixed hn _ (G.mix f g) (z.before Φ)
    ((d.fixed z hz).before Φ) (SingleMix.prefix_fixed d Φ z hz)
    ((d.extend_before Φ _).trans (congrArg (fun a => a.before Φ) (d.fixed_get z hz)))
  have h₁ := G.rho_mix_g_left f g (d.fixed z hz)
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem fixed_g_newL {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) :
    (newL d hn f g).rho .left (z.before Φ) = 2+g.rho .left (d.fixed z hz) := by
  have h₀ := G.rho_mix_g_left f (innerL d hn g) z
  have h₁ := d.rankL_fixed hn Δ g z (d.fixed z hz) hz (d.fixed_get z hz)
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem fixed_f_oldL {A : NormalForm P} (a : At Φ A) :
    (oldL d hn f g).rho .left (At.shift K a) = 2+f.rho .left a := by
  have h₀ := (d.extend Φ).rankL_fixed hn _ (G.mix f g) (At.shift K a)
    (At.shift F a) (SingleMix.suffix_fixed d Φ a) (d.extend_shift Φ a)
  have h₁ := G.rho_mix_f_left f g a
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem fixed_f_newL {A : NormalForm P} (a : At Φ A) :
    (newL d hn f g).rho .left (At.shift K a) = 1+f.rho .left a :=
  G.rho_mix_f_left f (innerL d hn g) a

theorem opposite_g_oldL {A : NormalForm P} (a : At Δ A) :
    (oldL d hn f g).rho .right (a.before Ψ) = 2+g.rho .right a := by
  have h₀ := (d.extend Φ).oppositeL hn (G.mix f g) (a.before Ψ)
  have h₁ := G.rho_mix_g_right f g a
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem opposite_g_newL {A : NormalForm P} (a : At Δ A) :
    (newL d hn f g).rho .right (a.before Ψ) = 2+g.rho .right a := by
  have h₀ := G.rho_mix_g_right f (innerL d hn g) a
  have h₁ := d.oppositeL hn g a
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem opposite_f_oldL {A : NormalForm P} (a : At Ψ A) :
    (oldL d hn f g).rho .right (At.shift Δ a) = 2+f.rho .right a := by
  have h₀ := (d.extend Φ).oppositeL hn (G.mix f g) (At.shift Δ a)
  have h₁ := G.rho_mix_f_right f g a
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem opposite_f_newL {A : NormalForm P} (a : At Ψ A) :
    (newL d hn f g).rho .right (At.shift Δ a) = 1+f.rho .right a :=
  G.rho_mix_f_right f (innerL d hn g) a
theorem opposite_g_equalL {A : NormalForm P} (a : At Δ A) :
    (oldL d hn f g).rho .right (a.before Ψ) = (newL d hn f g).rho .right (a.before Ψ) :=
  (opposite_g_oldL d hn f g a).trans (opposite_g_newL d hn f g a).symm
end L

section R
variable {Φ Ψ Δ : List (NormalForm P)} (f : G P Φ Ψ) (g : G P Δ F)
def rankInnerR := d.rankR hn Δ g
def rankOuterR := (d.extend Ψ).rankR hn _ (G.mix f g)
theorem selected_sumR :
    ((d.extend Ψ).selected.map (fun a => (G.mix f g).rho .right a)).sum =
      (d.selected.map (fun a => g.rho .right a)).sum+d.gs.length := by
  have ht := congrArg (fun xs : List (At (F++Ψ) d.C) =>
    (xs.map (fun a => (G.mix f g).rho .right a)).sum) (d.extend_selected Ψ)
  have hm : ((d.selected.map (fun a => a.before Ψ)).map
      (fun a => (G.mix f g).rho .right a)).sum =
      (d.selected.map (fun a => 1+g.rho .right a)).sum := by
    exact congrArg List.sum ((List.map_map ..).trans (List.map_congr_left (fun a _ => G.rho_mix_g_right f g a)))
  exact ht.trans (hm.trans ((G.sum_map_one_add d.selected (fun a => g.rho .right a)).trans
    (congrArg (fun n => (d.selected.map (fun a => g.rho .right a)).sum+n) d.selected_length)))
theorem contraction_lossR : rankOuterR d hn f g = rankInnerR d hn g+d.gs.length := by
  have ho := (d.extend Ψ).rankR_sum hn _ (G.mix f g)
  have hi := d.rankR_sum hn Δ g
  have hs := selected_sumR d f g
  change rankOuterR d hn f g = _ at ho
  change rankInnerR d hn g = _ at hi
  omega
theorem old_endpointR : (oldR d hn f g).rho .right (d.keep.before Ψ) = rankOuterR d hn f g := by
  have h := (d.extend Ψ).rankR_keep hn _ (G.mix f g)
  rw [d.extend_keep] at h
  exact h
theorem new_endpointR : (newR d hn f g).rho .right (d.keep.before Ψ) = rankInnerR d hn g+1 := by
  have h := G.rho_mix_g_right f (innerR d hn g) d.keep
  exact h.trans ((congrArg (fun n => 1+n) (d.rankR_keep hn Δ g)).trans (Nat.add_comm ..))
theorem endpoint_balanceR : (oldR d hn f g).rho .right (d.keep.before Ψ)+1 =
    (newR d hn f g).rho .right (d.keep.before Ψ)+d.gs.length := by
  have ho := old_endpointR d hn f g
  have he := new_endpointR d hn f g
  have hl := contraction_lossR d hn f g
  omega
theorem contraction_decreasesR : rankInnerR d hn g < rankOuterR d hn f g := by
  have h := contraction_lossR d hn f g
  omega
theorem endpoint_decreasesR : (newR d hn f g).rho .right (d.keep.before Ψ) < (oldR d hn f g).rho .right (d.keep.before Ψ) := by
  have h := endpoint_balanceR d hn f g
  omega

theorem fixed_g_oldR {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) :
    (oldR d hn f g).rho .right (z.before Ψ) = 2+g.rho .right (d.fixed z hz) := by
  have h₀ := (d.extend Ψ).rankR_fixed hn _ (G.mix f g) (z.before Ψ)
    ((d.fixed z hz).before Ψ) (SingleMix.prefix_fixed d Ψ z hz)
    ((d.extend_before Ψ _).trans (congrArg (fun a => a.before Ψ) (d.fixed_get z hz)))
  have h₁ := G.rho_mix_g_right f g (d.fixed z hz)
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem fixed_g_newR {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) :
    (newR d hn f g).rho .right (z.before Ψ) = 2+g.rho .right (d.fixed z hz) := by
  have h₀ := G.rho_mix_g_right f (innerR d hn g) z
  have h₁ := d.rankR_fixed hn Δ g z (d.fixed z hz) hz (d.fixed_get z hz)
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem fixed_f_oldR {A : NormalForm P} (a : At Ψ A) :
    (oldR d hn f g).rho .right (At.shift K a) = 2+f.rho .right a := by
  have h₀ := (d.extend Ψ).rankR_fixed hn _ (G.mix f g) (At.shift K a)
    (At.shift F a) (SingleMix.suffix_fixed d Ψ a) (d.extend_shift Ψ a)
  have h₁ := G.rho_mix_f_right f g a
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem fixed_f_newR {A : NormalForm P} (a : At Ψ A) :
    (newR d hn f g).rho .right (At.shift K a) = 1+f.rho .right a :=
  G.rho_mix_f_right f (innerR d hn g) a

theorem opposite_g_oldR {A : NormalForm P} (a : At Δ A) :
    (oldR d hn f g).rho .left (a.before Φ) = 2+g.rho .left a := by
  have h₀ := (d.extend Ψ).oppositeR hn (G.mix f g) (a.before Φ)
  have h₁ := G.rho_mix_g_left f g a
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem opposite_g_newR {A : NormalForm P} (a : At Δ A) :
    (newR d hn f g).rho .left (a.before Φ) = 2+g.rho .left a := by
  have h₀ := G.rho_mix_g_left f (innerR d hn g) a
  have h₁ := d.oppositeR hn g a
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem opposite_f_oldR {A : NormalForm P} (a : At Φ A) :
    (oldR d hn f g).rho .left (At.shift Δ a) = 2+f.rho .left a := by
  have h₀ := (d.extend Ψ).oppositeR hn (G.mix f g) (At.shift Δ a)
  have h₁ := G.rho_mix_f_left f g a
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem opposite_f_newR {A : NormalForm P} (a : At Φ A) :
    (newR d hn f g).rho .left (At.shift Δ a) = 1+f.rho .left a :=
  G.rho_mix_f_left f (innerR d hn g) a
theorem opposite_g_equalR {A : NormalForm P} (a : At Δ A) :
    (oldR d hn f g).rho .left (a.before Φ) = (newR d hn f g).rho .left (a.before Φ) :=
  (opposite_g_oldR d hn f g a).trans (opposite_g_newR d hn f g a).symm
end R

end DosenPetric.Reduced.Gentzen.W5.SinglePremiseMix
