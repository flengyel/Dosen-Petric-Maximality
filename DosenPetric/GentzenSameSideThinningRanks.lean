module

public import DosenPetric.GentzenSameSideThinning
public import DosenPetric.GentzenFixedContractionRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W1.SameSideThinning
universe u
variable {P : Type u} (d : GapInsertion.Data P) (hn : 2 ≤ d.gs0.length)

section Left
variable (Δ : List (NormalForm P)) (f : G P d.U0 Δ)

def rankNewL := G.contractionRankL d.C d.gs0 d.tail0 Δ hn (f.reindex d.upper0.symm rfl)
def rankOldL := G.contractionRankL d.C d.gs1 d.tail1 Δ (modifiedArity d hn)
  ((G.thinL d.upBefore d.upAfter Δ d.E f).reindex d.upper1.symm rfl)

theorem innerL_rank : (innerL d hn Δ f).rho .left d.keep0 = rankNewL d hn Δ f :=
  G.rho_reindex_left d.lower0 rfl _ _

theorem oldL_rank : (oldL d hn Δ f).rho .left d.keep1 = rankOldL d hn Δ f :=
  G.rho_reindex_left d.lower1 rfl _ _

theorem rankNewL_sum : rankNewL d hn Δ f = 1 +
    (d.selected0.map (fun (a : At d.U0 d.C) => f.rho .left a)).sum :=
  G.contractionRankL_cast_eq d.C d.gs0 d.tail0 hn d.upper0 f

theorem rankOldL_sum : rankOldL d hn Δ f = 1 +
    (d.selected1.map (fun (a : At d.U1 d.C) => (G.thinL d.upBefore d.upAfter Δ d.E f).rho .left a)).sum :=
  G.contractionRankL_cast_eq d.C d.gs1 d.tail1 (modifiedArity d hn) d.upper1 _

theorem contraction_lossL : rankOldL d hn Δ f = rankNewL d hn Δ f + d.gs0.length := by
  have h0 := rankNewL_sum d hn Δ f
  have h1 := rankOldL_sum d hn Δ f
  have he : d.selected1.map
      (fun (a : At d.U1 d.C) => (G.thinL d.upBefore d.upAfter Δ d.E f).rho .left a) =
      d.selected0.map (fun (a : At d.U0 d.C) => 1 + f.rho .left a) := by
    rw [d.selected_transport,List.map_map]
    apply List.map_congr_left
    intro a _
    exact G.rho_thinL_embedded d.upBefore d.upAfter Δ d.E f a
  rw [he] at h1
  have hs := G.sum_map_one_add d.selected0 (fun (a : At d.U0 d.C) => f.rho .left a)
  have hl := d.selected0_length
  omega

theorem endpoint_rankL : (newL d hn Δ f).rho .left d.keep1 = rankNewL d hn Δ f + 1 := by
  have h := G.rho_thinL_embedded d.loBefore d.loAfter Δ d.E (innerL d hn Δ f) d.keep0
  change (newL d hn Δ f).rho .left (d.tLower.get d.keep0) = 1 + (innerL d hn Δ f).rho .left d.keep0 at h
  rw [d.retained,innerL_rank] at h
  omega

theorem contraction_decreasesL : rankNewL d hn Δ f < rankOldL d hn Δ f := by
  have h := contraction_lossL d hn Δ f
  omega

theorem endpoint_lossL : (oldL d hn Δ f).rho .left d.keep1 + 1 =
    (newL d hn Δ f).rho .left d.keep1 + d.gs0.length := by
  have h0 := oldL_rank d hn Δ f
  have h1 := contraction_lossL d hn Δ f
  have h2 := endpoint_rankL d hn Δ f
  omega

theorem endpoint_decreasesL : (newL d hn Δ f).rho .left d.keep1 < (oldL d hn Δ f).rho .left d.keep1 := by
  have h := endpoint_lossL d hn Δ f
  omega

theorem inserted_newL_rank : (newL d hn Δ f).rho .left d.zLower = 1 :=
  G.rho_thinL_principal d.loBefore d.loAfter Δ d.E (innerL d hn Δ f)

theorem inserted_oldL_rank : (oldL d hn Δ f).rho .left d.zLower = 2 := by
  change ((G.contractL d.C d.gs1 d.tail1 Δ (modifiedArity d hn)
    ((G.thinL d.upBefore d.upAfter Δ d.E f).reindex d.upper1.symm rfl)).reindex d.lower1 rfl).rho .left d.zLower = 2
  rw [G.rho_reindex_left_at]
  rw [G.contraction_fixed_left d.C d.gs1 d.tail1 Δ (modifiedArity d hn) _ _ _
    d.canonical_inserted_fixed d.canonical_inserted]
  rw [G.rho_reindex_left]
  exact congrArg (fun n : Nat => 1+n) (G.rho_thinL_principal d.upBefore d.upAfter Δ d.E f)

end Left

section Right
variable (Γ : List (NormalForm P)) (f : G P Γ d.U0)

def rankNewR := G.contractionRankR Γ d.C d.gs0 d.tail0 hn (f.reindex rfl d.upper0.symm)
def rankOldR := G.contractionRankR Γ d.C d.gs1 d.tail1 (modifiedArity d hn)
  ((G.thinR Γ d.upBefore d.upAfter d.E f).reindex rfl d.upper1.symm)

theorem innerR_rank : (innerR d hn Γ f).rho .right d.keep0 = rankNewR d hn Γ f :=
  G.rho_reindex_right rfl d.lower0 _ _

theorem oldR_rank : (oldR d hn Γ f).rho .right d.keep1 = rankOldR d hn Γ f :=
  G.rho_reindex_right rfl d.lower1 _ _

theorem rankNewR_sum : rankNewR d hn Γ f = 1 +
    (d.selected0.map (fun (a : At d.U0 d.C) => f.rho .right a)).sum :=
  G.contractionRankR_cast_eq d.C d.gs0 d.tail0 hn d.upper0 f

theorem rankOldR_sum : rankOldR d hn Γ f = 1 +
    (d.selected1.map (fun (a : At d.U1 d.C) => (G.thinR Γ d.upBefore d.upAfter d.E f).rho .right a)).sum :=
  G.contractionRankR_cast_eq d.C d.gs1 d.tail1 (modifiedArity d hn) d.upper1 _

theorem contraction_lossR : rankOldR d hn Γ f = rankNewR d hn Γ f + d.gs0.length := by
  have h0 := rankNewR_sum d hn Γ f
  have h1 := rankOldR_sum d hn Γ f
  have he : d.selected1.map
      (fun (a : At d.U1 d.C) => (G.thinR Γ d.upBefore d.upAfter d.E f).rho .right a) =
      d.selected0.map (fun (a : At d.U0 d.C) => 1 + f.rho .right a) := by
    rw [d.selected_transport,List.map_map]
    apply List.map_congr_left
    intro a _
    exact G.rho_thinR_embedded Γ d.upBefore d.upAfter d.E f a
  rw [he] at h1
  have hs := G.sum_map_one_add d.selected0 (fun (a : At d.U0 d.C) => f.rho .right a)
  have hl := d.selected0_length
  omega

theorem endpoint_rankR : (newR d hn Γ f).rho .right d.keep1 = rankNewR d hn Γ f + 1 := by
  have h := G.rho_thinR_embedded Γ d.loBefore d.loAfter d.E (innerR d hn Γ f) d.keep0
  change (newR d hn Γ f).rho .right (d.tLower.get d.keep0) = 1 + (innerR d hn Γ f).rho .right d.keep0 at h
  rw [d.retained,innerR_rank] at h
  omega

theorem contraction_decreasesR : rankNewR d hn Γ f < rankOldR d hn Γ f := by
  have h := contraction_lossR d hn Γ f
  omega

theorem endpoint_lossR : (oldR d hn Γ f).rho .right d.keep1 + 1 =
    (newR d hn Γ f).rho .right d.keep1 + d.gs0.length := by
  have h0 := oldR_rank d hn Γ f
  have h1 := contraction_lossR d hn Γ f
  have h2 := endpoint_rankR d hn Γ f
  omega

theorem endpoint_decreasesR : (newR d hn Γ f).rho .right d.keep1 < (oldR d hn Γ f).rho .right d.keep1 := by
  have h := endpoint_lossR d hn Γ f
  omega

theorem inserted_newR_rank : (newR d hn Γ f).rho .right d.zLower = 1 :=
  G.rho_thinR_principal Γ d.loBefore d.loAfter d.E (innerR d hn Γ f)

theorem inserted_oldR_rank : (oldR d hn Γ f).rho .right d.zLower = 2 := by
  change ((G.contractR Γ d.C d.gs1 d.tail1 (modifiedArity d hn)
    ((G.thinR Γ d.upBefore d.upAfter d.E f).reindex rfl d.upper1.symm)).reindex rfl d.lower1).rho .right d.zLower = 2
  rw [G.rho_reindex_right_at]
  rw [G.contraction_fixed_right Γ d.C d.gs1 d.tail1 (modifiedArity d hn) _ _ _
    d.canonical_inserted_fixed d.canonical_inserted]
  rw [G.rho_reindex_right]
  exact congrArg (fun n : Nat => 1+n) (G.rho_thinR_principal Γ d.upBefore d.upAfter d.E f)

end Right

end DosenPetric.Reduced.Gentzen.W1.SameSideThinning
