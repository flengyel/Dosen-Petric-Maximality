module

public import DosenPetric.GentzenMixedContractionBlocked
public import DosenPetric.GentzenSelectionRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.MixedPremiseMix
universe u
variable {P : Type u} {C : NormalForm P} {F K U L : List (NormalForm P)}
variable (p : ContractionSelection C F K) (q : ContractionSelection C U L)

section Left
variable {Δ Λ : List (NormalForm P)} (f : G P U Δ) (g : G P F Λ)
theorem old_rankL : (oldL p q f g).rho .left (p.chain q).keep =
    1+(p.selected.map (fun a => g.rho .left a)).sum+
      (q.selected.map (fun a => f.rho .left a)).sum+p.arity+q.arity := by
  let r : At F C → Nat := fun a => g.rho .left a
  let s : At U C → Nat := fun a => f.rho .left a
  have hk := (p.chain q).block.rankL_keep (total_bound p q) _ (G.mix f g)
  have hs := (p.chain q).block.rankL_sum (total_bound p q) _ (G.mix f g)
  rw [←ContractionSelection.keep_eq] at hk
  rw [←ContractionSelection.selected_eq,ContractionSelection.chain_selected] at hs
  change (p.chain q).block.rankL (total_bound p q) _ (G.mix f g) =
    1+((p.selected.map (fun a => a.before U)++q.selected.map (At.shift F)).map
      (fun a : At (F++U) C => (G.mix f g).rho .left a)).sum at hs
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def,
    G.rho_mix_g_left,G.rho_mix_f_left] at hs
  change (p.chain q).block.rankL (total_bound p q) _ (G.mix f g) =
    1+((p.selected.map (fun a => 1+r a)).sum+
      (q.selected.map (fun a => 1+s a)).sum) at hs
  rw [G.sum_map_one_add,G.sum_map_one_add,p.selected_length,q.selected_length] at hs
  change (oldL p q f g).rho .left (p.chain q).keep = _ at hk
  change (oldL p q f g).rho .left (p.chain q).keep =
    1+(p.selected.map r).sum+(q.selected.map s).sum+p.arity+q.arity
  omega

theorem new_rankL : (newL p q f g).rho .left (p.chain q).keep =
    3+(p.performL Λ g).rho .left p.keep+(q.performL Δ f).rho .left q.keep := by
  have hk := (p.mergeBlock q).rankL_keep (Nat.le_refl 2) _ (middleL p q f g)
  have hs := (p.mergeBlock q).rankL_sum (Nat.le_refl 2) _ (middleL p q f g)
  rw [p.merge_retained q] at hk
  rw [p.merge_selected q] at hs
  change _ = 1+((middleL p q f g).rho .left (p.keep.before L)+
    ((middleL p q f g).rho .left (At.shift K q.keep)+0)) at hs
  have hp := G.rho_mix_g_left (q.performL Δ f) (p.performL Λ g) p.keep
  have hq := G.rho_mix_f_left (q.performL Δ f) (p.performL Λ g) q.keep
  change (newL p q f g).rho .left (p.chain q).keep = _ at hk
  change (middleL p q f g).rho .left (p.keep.before L) = _ at hp
  change (middleL p q f g).rho .left (At.shift K q.keep) = _ at hq
  omega

theorem endpoint_leL : (newL p q f g).rho .left (p.chain q).keep ≤
    (oldL p q f g).rho .left (p.chain q).keep := by
  rw [old_rankL,new_rankL,p.performL_rank,q.performL_rank]
  have hp:=p.overhead_bound
  have hq:=q.overhead_bound
  omega
end Left

section Right
variable {Δ Λ : List (NormalForm P)} (f : G P Δ U) (g : G P Λ F)
theorem old_rankR : (oldR p q f g).rho .right (p.chain q).keep =
    1+(p.selected.map (fun a => g.rho .right a)).sum+
      (q.selected.map (fun a => f.rho .right a)).sum+p.arity+q.arity := by
  let r : At F C → Nat := fun a => g.rho .right a
  let s : At U C → Nat := fun a => f.rho .right a
  have hk := (p.chain q).block.rankR_keep (total_bound p q) _ (G.mix f g)
  have hs := (p.chain q).block.rankR_sum (total_bound p q) _ (G.mix f g)
  rw [←ContractionSelection.keep_eq] at hk
  rw [←ContractionSelection.selected_eq,ContractionSelection.chain_selected] at hs
  change (p.chain q).block.rankR (total_bound p q) _ (G.mix f g) =
    1+((p.selected.map (fun a => a.before U)++q.selected.map (At.shift F)).map
      (fun a : At (F++U) C => (G.mix f g).rho .right a)).sum at hs
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def,
    G.rho_mix_g_right,G.rho_mix_f_right] at hs
  change (p.chain q).block.rankR (total_bound p q) _ (G.mix f g) =
    1+((p.selected.map (fun a => 1+r a)).sum+
      (q.selected.map (fun a => 1+s a)).sum) at hs
  rw [G.sum_map_one_add,G.sum_map_one_add,p.selected_length,q.selected_length] at hs
  change (oldR p q f g).rho .right (p.chain q).keep = _ at hk
  change (oldR p q f g).rho .right (p.chain q).keep =
    1+(p.selected.map r).sum+(q.selected.map s).sum+p.arity+q.arity
  omega

theorem new_rankR : (newR p q f g).rho .right (p.chain q).keep =
    3+(p.performR Λ g).rho .right p.keep+(q.performR Δ f).rho .right q.keep := by
  have hk := (p.mergeBlock q).rankR_keep (Nat.le_refl 2) _ (middleR p q f g)
  have hs := (p.mergeBlock q).rankR_sum (Nat.le_refl 2) _ (middleR p q f g)
  rw [p.merge_retained q] at hk
  rw [p.merge_selected q] at hs
  change _ = 1+((middleR p q f g).rho .right (p.keep.before L)+
    ((middleR p q f g).rho .right (At.shift K q.keep)+0)) at hs
  have hp := G.rho_mix_g_right (q.performR Δ f) (p.performR Λ g) p.keep
  have hq := G.rho_mix_f_right (q.performR Δ f) (p.performR Λ g) q.keep
  change (newR p q f g).rho .right (p.chain q).keep = _ at hk
  change (middleR p q f g).rho .right (p.keep.before L) = _ at hp
  change (middleR p q f g).rho .right (At.shift K q.keep) = _ at hq
  omega

theorem endpoint_leR : (newR p q f g).rho .right (p.chain q).keep ≤
    (oldR p q f g).rho .right (p.chain q).keep := by
  rw [old_rankR,new_rankR,p.performR_rank,q.performR_rank]
  have hp:=p.overhead_bound
  have hq:=q.overhead_bound
  omega
end Right

end DosenPetric.Reduced.Gentzen.W5.MixedPremiseMix
