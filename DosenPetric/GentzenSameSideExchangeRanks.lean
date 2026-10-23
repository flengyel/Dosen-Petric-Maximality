module

public import DosenPetric.GentzenSameSideExchange
public import DosenPetric.GentzenFixedContractionRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W1.SameSideExchange
universe u
variable {P : Type u} (d : GapExchange.Data P) (hn : 2 ≤ d.gs0.length)

section Left
variable (Δ : List (NormalForm P)) (f : G P d.U0 Δ)

def rankNewL := G.contractionRankL d.C d.gs0 d.tail0 Δ hn (f.reindex d.upper0.symm rfl)
def rankOldL := G.contractionRankL d.C d.gs1 d.tail1 Δ (modifiedArity d hn)
  ((G.exchangeL d.upBefore d.X d.Y d.upAfter Δ f).reindex d.upper1.symm rfl)

theorem innerL_rank : (innerL d hn Δ f).rho .left d.keep0 = rankNewL d hn Δ f :=
  G.rho_reindex_left d.lower0 rfl _ _

theorem oldL_rank : (oldL d hn Δ f).rho .left d.keep1 = rankOldL d hn Δ f :=
  G.rho_reindex_left d.lower1 rfl _ _

theorem rankNewL_sum : rankNewL d hn Δ f = 1 +
    (d.selected0.map (fun (a : At d.U0 d.C) => f.rho .left a)).sum :=
  G.contractionRankL_cast_eq d.C d.gs0 d.tail0 hn d.upper0 f

theorem rankOldL_sum : rankOldL d hn Δ f = 1 +
    (d.selected1.map (fun (a : At d.U1 d.C) => (G.exchangeL d.upBefore d.X d.Y d.upAfter Δ f).rho .left a)).sum :=
  G.contractionRankL_cast_eq d.C d.gs1 d.tail1 (modifiedArity d hn) d.upper1 _

theorem contraction_lossL : rankOldL d hn Δ f = rankNewL d hn Δ f + d.gs0.length := by
  have h0 := rankNewL_sum d hn Δ f
  have h1 := rankOldL_sum d hn Δ f
  have he : d.selected1.map
      (fun (a : At d.U1 d.C) => (G.exchangeL d.upBefore d.X d.Y d.upAfter Δ f).rho .left a) =
      d.selected0.map (fun (a : At d.U0 d.C) => 1 + f.rho .left a) := by
    rw [d.selected_transport,List.map_map]
    apply List.map_congr_left
    intro a _
    exact G.rho_exchangeL_embedded d.upBefore d.X d.Y d.upAfter Δ f a
  rw [he] at h1
  have hs : (d.selected0.map (fun (a : At d.U0 d.C) => 1 + f.rho .left a)).sum =
      (d.selected0.map (fun (a : At d.U0 d.C) => f.rho .left a)).sum + d.selected0.length :=
    G.sum_map_one_add d.selected0 (fun (a : At d.U0 d.C) => f.rho .left a)
  have hl := d.selected0_length
  omega

theorem endpoint_rankL : (newL d hn Δ f).rho .left d.keep1 = rankNewL d hn Δ f + 1 := by
  have h := G.rho_exchangeL_embedded d.loBefore d.X d.Y d.loAfter Δ (innerL d hn Δ f) d.keep0
  change (newL d hn Δ f).rho .left (d.swapLower d.keep0) = 1 + (innerL d hn Δ f).rho .left d.keep0 at h
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

end Left

section Right
variable (Γ : List (NormalForm P)) (f : G P Γ d.U0)

def rankNewR := G.contractionRankR Γ d.C d.gs0 d.tail0 hn (f.reindex rfl d.upper0.symm)
def rankOldR := G.contractionRankR Γ d.C d.gs1 d.tail1 (modifiedArity d hn)
  ((G.exchangeR Γ d.upBefore d.X d.Y d.upAfter f).reindex rfl d.upper1.symm)

theorem innerR_rank : (innerR d hn Γ f).rho .right d.keep0 = rankNewR d hn Γ f :=
  G.rho_reindex_right rfl d.lower0 _ _

theorem oldR_rank : (oldR d hn Γ f).rho .right d.keep1 = rankOldR d hn Γ f :=
  G.rho_reindex_right rfl d.lower1 _ _

theorem rankNewR_sum : rankNewR d hn Γ f = 1 +
    (d.selected0.map (fun (a : At d.U0 d.C) => f.rho .right a)).sum :=
  G.contractionRankR_cast_eq d.C d.gs0 d.tail0 hn d.upper0 f

theorem rankOldR_sum : rankOldR d hn Γ f = 1 +
    (d.selected1.map (fun (a : At d.U1 d.C) => (G.exchangeR Γ d.upBefore d.X d.Y d.upAfter f).rho .right a)).sum :=
  G.contractionRankR_cast_eq d.C d.gs1 d.tail1 (modifiedArity d hn) d.upper1 _

theorem contraction_lossR : rankOldR d hn Γ f = rankNewR d hn Γ f + d.gs0.length := by
  have h0 := rankNewR_sum d hn Γ f
  have h1 := rankOldR_sum d hn Γ f
  have he : d.selected1.map
      (fun (a : At d.U1 d.C) => (G.exchangeR Γ d.upBefore d.X d.Y d.upAfter f).rho .right a) =
      d.selected0.map (fun (a : At d.U0 d.C) => 1 + f.rho .right a) := by
    rw [d.selected_transport,List.map_map]
    apply List.map_congr_left
    intro a _
    exact G.rho_exchangeR_embedded Γ d.upBefore d.X d.Y d.upAfter f a
  rw [he] at h1
  have hs : (d.selected0.map (fun (a : At d.U0 d.C) => 1 + f.rho .right a)).sum =
      (d.selected0.map (fun (a : At d.U0 d.C) => f.rho .right a)).sum + d.selected0.length :=
    G.sum_map_one_add d.selected0 (fun (a : At d.U0 d.C) => f.rho .right a)
  have hl := d.selected0_length
  omega

theorem endpoint_rankR : (newR d hn Γ f).rho .right d.keep1 = rankNewR d hn Γ f + 1 := by
  have h := G.rho_exchangeR_embedded Γ d.loBefore d.X d.Y d.loAfter (innerR d hn Γ f) d.keep0
  change (newR d hn Γ f).rho .right (d.swapLower d.keep0) = 1 + (innerR d hn Γ f).rho .right d.keep0 at h
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

end Right

end DosenPetric.Reduced.Gentzen.W1.SameSideExchange
