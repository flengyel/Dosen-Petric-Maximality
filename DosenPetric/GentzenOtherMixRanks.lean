module

public import DosenPetric.GentzenOtherMixRules
public import DosenPetric.GentzenMixRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.OtherPremiseMix
universe u
variable {P : Type u} {F K : List (NormalForm P)}
variable (d : ContractionBlock P F K) (hn : 2 ≤ d.gs.length)

section L
variable {Φ Ψ Δ : List (NormalForm P)} (f : G P Φ Ψ) (g : G P F Δ)
def rankInnerL := d.rankL hn Δ g
def rankOuterL := (d.prepend hn Φ).rankL (d.prepend_bound hn Φ) _ (G.mix g f)
theorem selected_sumL :
    ((d.prepend hn Φ).selected.map (fun a => (G.mix g f).rho .left a)).sum =
      (d.selected.map (fun a => g.rho .left a)).sum+d.gs.length := by
  have ht := congrArg (fun xs : List (At (Φ++F) d.C) =>
    (xs.map (fun a => (G.mix g f).rho .left a)).sum) (d.prepend_selected hn Φ)
  have hm : ((d.selected.map (At.shift Φ)).map
      (fun a => (G.mix g f).rho .left a)).sum =
      (d.selected.map (fun a => 1+g.rho .left a)).sum := by
    exact congrArg List.sum ((List.map_map ..).trans (List.map_congr_left (fun a _ => G.rho_mix_f_left g f a)))
  exact ht.trans (hm.trans ((G.sum_map_one_add d.selected (fun a => g.rho .left a)).trans
    (congrArg (fun n => (d.selected.map (fun a => g.rho .left a)).sum+n) d.selected_length)))
theorem contraction_lossL : rankOuterL d hn f g = rankInnerL d hn g+d.gs.length := by
  have ho := (d.prepend hn Φ).rankL_sum (d.prepend_bound hn Φ) _ (G.mix g f)
  have hi := d.rankL_sum hn Δ g
  have hs := selected_sumL d hn f g
  change rankOuterL d hn f g = _ at ho
  change rankInnerL d hn g = _ at hi
  omega
theorem old_endpointL : (oldL d hn f g).rho .left (At.shift Φ d.keep) = rankOuterL d hn f g := by
  have h := (d.prepend hn Φ).rankL_keep (d.prepend_bound hn Φ) _ (G.mix g f)
  rw [d.prepend_keep] at h
  exact h
theorem new_endpointL : (newL d hn f g).rho .left (At.shift Φ d.keep) = rankInnerL d hn g+1 := by
  have h := G.rho_mix_f_left (innerL d hn g) f d.keep
  exact h.trans ((congrArg (fun n => 1+n) (d.rankL_keep hn Δ g)).trans (Nat.add_comm ..))
theorem endpoint_balanceL : (oldL d hn f g).rho .left (At.shift Φ d.keep)+1 =
    (newL d hn f g).rho .left (At.shift Φ d.keep)+d.gs.length := by
  have ho := old_endpointL d hn f g
  have he := new_endpointL d hn f g
  have hl := contraction_lossL d hn f g
  omega
theorem contraction_decreasesL : rankInnerL d hn g < rankOuterL d hn f g := by
  have h := contraction_lossL d hn f g
  omega
theorem endpoint_decreasesL : (newL d hn f g).rho .left (At.shift Φ d.keep) < (oldL d hn f g).rho .left (At.shift Φ d.keep) := by
  have h := endpoint_balanceL d hn f g
  omega

theorem fixed_g_oldL {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) :
    (oldL d hn f g).rho .left (At.shift Φ z) = 2+g.rho .left (d.fixed z hz) := by
  have h₀ := (d.prepend hn Φ).rankL_fixed (d.prepend_bound hn Φ) _ (G.mix g f) (At.shift Φ z)
    (At.shift Φ (d.fixed z hz)) (OtherMix.suffix_fixed d hn Φ z hz)
    ((d.prepend_shift hn Φ _).trans (congrArg (At.shift Φ) (d.fixed_get z hz)))
  have h₁ := G.rho_mix_f_left g f (d.fixed z hz)
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem fixed_g_newL {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) :
    (newL d hn f g).rho .left (At.shift Φ z) = 2+g.rho .left (d.fixed z hz) := by
  have h₀ := G.rho_mix_f_left (innerL d hn g) f z
  have h₁ := d.rankL_fixed hn Δ g z (d.fixed z hz) hz (d.fixed_get z hz)
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem fixed_f_oldL {A : NormalForm P} (a : At Φ A) :
    (oldL d hn f g).rho .left (a.before K) = 2+f.rho .left a := by
  have h₀ := (d.prepend hn Φ).rankL_fixed (d.prepend_bound hn Φ) _ (G.mix g f) (a.before K)
    (a.before F) (OtherMix.prefix_fixed d hn Φ a) (d.prepend_before hn Φ a)
  have h₁ := G.rho_mix_g_left g f a
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem fixed_f_newL {A : NormalForm P} (a : At Φ A) :
    (newL d hn f g).rho .left (a.before K) = 1+f.rho .left a :=
  G.rho_mix_g_left (innerL d hn g) f a

theorem opposite_g_oldL {A : NormalForm P} (a : At Δ A) :
    (oldL d hn f g).rho .right (At.shift Ψ a) = 2+g.rho .right a := by
  have h₀ := (d.prepend hn Φ).oppositeL (d.prepend_bound hn Φ) (G.mix g f) (At.shift Ψ a)
  have h₁ := G.rho_mix_f_right g f a
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem opposite_g_newL {A : NormalForm P} (a : At Δ A) :
    (newL d hn f g).rho .right (At.shift Ψ a) = 2+g.rho .right a := by
  have h₀ := G.rho_mix_f_right (innerL d hn g) f a
  have h₁ := d.oppositeL hn g a
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem opposite_f_oldL {A : NormalForm P} (a : At Ψ A) :
    (oldL d hn f g).rho .right (a.before Δ) = 2+f.rho .right a := by
  have h₀ := (d.prepend hn Φ).oppositeL (d.prepend_bound hn Φ) (G.mix g f) (a.before Δ)
  have h₁ := G.rho_mix_g_right g f a
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem opposite_f_newL {A : NormalForm P} (a : At Ψ A) :
    (newL d hn f g).rho .right (a.before Δ) = 1+f.rho .right a :=
  G.rho_mix_g_right (innerL d hn g) f a
theorem opposite_g_equalL {A : NormalForm P} (a : At Δ A) :
    (oldL d hn f g).rho .right (At.shift Ψ a) = (newL d hn f g).rho .right (At.shift Ψ a) :=
  (opposite_g_oldL d hn f g a).trans (opposite_g_newL d hn f g a).symm
end L

section R
variable {Φ Ψ Δ : List (NormalForm P)} (f : G P Φ Ψ) (g : G P Δ F)
def rankInnerR := d.rankR hn Δ g
def rankOuterR := (d.prepend hn Ψ).rankR (d.prepend_bound hn Ψ) _ (G.mix g f)
theorem selected_sumR :
    ((d.prepend hn Ψ).selected.map (fun a => (G.mix g f).rho .right a)).sum =
      (d.selected.map (fun a => g.rho .right a)).sum+d.gs.length := by
  have ht := congrArg (fun xs : List (At (Ψ++F) d.C) =>
    (xs.map (fun a => (G.mix g f).rho .right a)).sum) (d.prepend_selected hn Ψ)
  have hm : ((d.selected.map (At.shift Ψ)).map
      (fun a => (G.mix g f).rho .right a)).sum =
      (d.selected.map (fun a => 1+g.rho .right a)).sum := by
    exact congrArg List.sum ((List.map_map ..).trans (List.map_congr_left (fun a _ => G.rho_mix_f_right g f a)))
  exact ht.trans (hm.trans ((G.sum_map_one_add d.selected (fun a => g.rho .right a)).trans
    (congrArg (fun n => (d.selected.map (fun a => g.rho .right a)).sum+n) d.selected_length)))
theorem contraction_lossR : rankOuterR d hn f g = rankInnerR d hn g+d.gs.length := by
  have ho := (d.prepend hn Ψ).rankR_sum (d.prepend_bound hn Ψ) _ (G.mix g f)
  have hi := d.rankR_sum hn Δ g
  have hs := selected_sumR d hn f g
  change rankOuterR d hn f g = _ at ho
  change rankInnerR d hn g = _ at hi
  omega
theorem old_endpointR : (oldR d hn f g).rho .right (At.shift Ψ d.keep) = rankOuterR d hn f g := by
  have h := (d.prepend hn Ψ).rankR_keep (d.prepend_bound hn Ψ) _ (G.mix g f)
  rw [d.prepend_keep] at h
  exact h
theorem new_endpointR : (newR d hn f g).rho .right (At.shift Ψ d.keep) = rankInnerR d hn g+1 := by
  have h := G.rho_mix_f_right (innerR d hn g) f d.keep
  exact h.trans ((congrArg (fun n => 1+n) (d.rankR_keep hn Δ g)).trans (Nat.add_comm ..))
theorem endpoint_balanceR : (oldR d hn f g).rho .right (At.shift Ψ d.keep)+1 =
    (newR d hn f g).rho .right (At.shift Ψ d.keep)+d.gs.length := by
  have ho := old_endpointR d hn f g
  have he := new_endpointR d hn f g
  have hl := contraction_lossR d hn f g
  omega
theorem contraction_decreasesR : rankInnerR d hn g < rankOuterR d hn f g := by
  have h := contraction_lossR d hn f g
  omega
theorem endpoint_decreasesR : (newR d hn f g).rho .right (At.shift Ψ d.keep) < (oldR d hn f g).rho .right (At.shift Ψ d.keep) := by
  have h := endpoint_balanceR d hn f g
  omega

theorem fixed_g_oldR {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) :
    (oldR d hn f g).rho .right (At.shift Ψ z) = 2+g.rho .right (d.fixed z hz) := by
  have h₀ := (d.prepend hn Ψ).rankR_fixed (d.prepend_bound hn Ψ) _ (G.mix g f) (At.shift Ψ z)
    (At.shift Ψ (d.fixed z hz)) (OtherMix.suffix_fixed d hn Ψ z hz)
    ((d.prepend_shift hn Ψ _).trans (congrArg (At.shift Ψ) (d.fixed_get z hz)))
  have h₁ := G.rho_mix_f_right g f (d.fixed z hz)
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem fixed_g_newR {A : NormalForm P} (z : At K A) (hz : z.index ≠ d.keep.index) :
    (newR d hn f g).rho .right (At.shift Ψ z) = 2+g.rho .right (d.fixed z hz) := by
  have h₀ := G.rho_mix_f_right (innerR d hn g) f z
  have h₁ := d.rankR_fixed hn Δ g z (d.fixed z hz) hz (d.fixed_get z hz)
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem fixed_f_oldR {A : NormalForm P} (a : At Ψ A) :
    (oldR d hn f g).rho .right (a.before K) = 2+f.rho .right a := by
  have h₀ := (d.prepend hn Ψ).rankR_fixed (d.prepend_bound hn Ψ) _ (G.mix g f) (a.before K)
    (a.before F) (OtherMix.prefix_fixed d hn Ψ a) (d.prepend_before hn Ψ a)
  have h₁ := G.rho_mix_g_right g f a
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem fixed_f_newR {A : NormalForm P} (a : At Ψ A) :
    (newR d hn f g).rho .right (a.before K) = 1+f.rho .right a :=
  G.rho_mix_g_right (innerR d hn g) f a

theorem opposite_g_oldR {A : NormalForm P} (a : At Δ A) :
    (oldR d hn f g).rho .left (At.shift Φ a) = 2+g.rho .left a := by
  have h₀ := (d.prepend hn Ψ).oppositeR (d.prepend_bound hn Ψ) (G.mix g f) (At.shift Φ a)
  have h₁ := G.rho_mix_f_left g f a
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem opposite_g_newR {A : NormalForm P} (a : At Δ A) :
    (newR d hn f g).rho .left (At.shift Φ a) = 2+g.rho .left a := by
  have h₀ := G.rho_mix_f_left (innerR d hn g) f a
  have h₁ := d.oppositeR hn g a
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem opposite_f_oldR {A : NormalForm P} (a : At Φ A) :
    (oldR d hn f g).rho .left (a.before Δ) = 2+f.rho .left a := by
  have h₀ := (d.prepend hn Ψ).oppositeR (d.prepend_bound hn Ψ) (G.mix g f) (a.before Δ)
  have h₁ := G.rho_mix_g_left g f a
  exact h₀.trans ((congrArg (fun n => 1+n) h₁).trans (by omega))
theorem opposite_f_newR {A : NormalForm P} (a : At Φ A) :
    (newR d hn f g).rho .left (a.before Δ) = 1+f.rho .left a :=
  G.rho_mix_g_left (innerR d hn g) f a
theorem opposite_g_equalR {A : NormalForm P} (a : At Δ A) :
    (oldR d hn f g).rho .left (At.shift Φ a) = (newR d hn f g).rho .left (At.shift Φ a) :=
  (opposite_g_oldR d hn f g a).trans (opposite_g_newR d hn f g a).symm
end R

end DosenPetric.Reduced.Gentzen.W5.OtherPremiseMix
