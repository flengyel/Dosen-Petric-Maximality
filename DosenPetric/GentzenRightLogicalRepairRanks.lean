module

public import DosenPetric.GentzenRightLogicalRepairComponents

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W4.HeadRight
universe u
variable {P : Type u} (d : Gentzen.SelectedLogical.Data P .disj)
variable (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ d.F)

theorem moved_rank : (movedR d hn Γ f).rho .right (At.shift [d.A,d.B] d.s.inner.keep) =
    W4.SelectedLogical.rankInnerR d hn Γ f+1 := by
  have h := UnaryCast.exchangeR_embedded [] d.s.I [d.A,d.B] []
    (moveSource d) (moveTarget d) Γ (W4.SelectedLogical.innerR d hn Γ f)
      (d.s.inner.keep.before [d.A,d.B])
  change (movedR d hn Γ f).rho .right ((moveRoute d).get _) = _ at h
  rw [move_prefix] at h
  have hk := d.inner.rankR_keep hn Γ f
  rw [ContractionBlock.extend_keep] at hk
  change (W4.SelectedLogical.innerR d hn Γ f).rho .right
    (d.s.inner.keep.before [d.A,d.B]) = _ at hk
  rw [hk] at h
  change (movedR d hn Γ f).rho .right (At.shift [d.A,d.B] d.s.inner.keep) =
    1+W4.SelectedLogical.rankInnerR d hn Γ f at h
  omega

theorem head_retained_rank : (headR d hn Γ f).rho .right d.s.inner.keep.there =
    W4.SelectedLogical.rankInnerR d hn Γ f+2 := by
  have hp : At.fixed [] [d.A,d.B] [d.C] d.s.I
      (At.shift [d.A,d.B] d.s.inner.keep) = some d.s.inner.keep.there :=
    At.fixed_tail [] [d.A,d.B] [d.C] d.s.I d.s.inner.keep
  have h := G.rho_disjR_surviving Γ [] d.s.I d.A d.B (movedR d hn Γ f) _ _ hp
  change (headR d hn Γ f).rho .right d.s.inner.keep.there = _ at h
  rw [moved_rank] at h
  omega

theorem head_principal_rank : (headR d hn Γ f).rho .right (.here d.C d.s.I) = 1 :=
  G.rho_disjR_principal Γ [] d.s.I d.A d.B (movedR d hn Γ f)

theorem blocked_rank : (blockedR d hn Γ f).rho .right d.s.inner.keep =
    W4.SelectedLogical.rankInnerR d hn Γ f+4 := by
  have hk := (block d).rankR_keep (Nat.le_refl 2) Γ (headR d hn Γ f)
  have hs := (block d).rankR_sum (Nat.le_refl 2) Γ (headR d hn Γ f)
  rw [block_keep] at hk
  rw [block_selected] at hs
  change (block d).rankR (Nat.le_refl 2) Γ (headR d hn Γ f) =
    1+((headR d hn Γ f).rho .right (.here d.C d.s.I)+
      ((headR d hn Γ f).rho .right d.s.inner.keep.there+0)) at hs
  rw [head_retained_rank,head_principal_rank] at hs
  change (blockedR d hn Γ f).rho .right d.s.inner.keep = _ at hk
  omega

theorem repair_rank : (repairR d hn Γ f).rho .right d.x =
    W4.SelectedLogical.rankInnerR d hn Γ f+5 := by
  have h := UnaryCast.exchangeR_embedded (gaps d.gs) [d.C] d.Θ []
    d.s.exchangeSource d.s.exchangeTarget Γ (blockedR d hn Γ f) d.s.inner.keep
  change (repairR d hn Γ f).rho .right (d.s.e.get d.s.inner.keep) = _ at h
  rw [d.s.retained] at h
  change (repairR d hn Γ f).rho .right d.x =
    1+(blockedR d hn Γ f).rho .right d.s.inner.keep at h
  rw [blocked_rank] at h
  omega

end DosenPetric.Reduced.Gentzen.W4.HeadRight
