module

public import DosenPetric.GentzenRightLogicalRepairRanks
public import DosenPetric.GentzenContractionBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W4.HeadRight
universe u
variable {P : Type u} (d : Gentzen.SelectedLogical.Data P .disj)
variable (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ d.F)

theorem inner_bound : ContractionBound .right d.C
    (W4.SelectedLogical.rankInnerR d hn Γ f+1) (W4.SelectedLogical.innerR d hn Γ f)
    (fun a => a.index = d.s.inner.keep.index) := by
  apply ContractionBound.bounded
  intro a ha
  change At d.I d.C at a
  have he : a = d.inner.keep := At.index_injective _ _ (by
    rw [ContractionBlock.extend_keep,At.index_before]; exact ha)
  subst a
  have h := d.inner.rankR_keep hn Γ f
  change (W4.SelectedLogical.innerR d hn Γ f).rho .right d.inner.keep =
    W4.SelectedLogical.rankInnerR d hn Γ f at h
  omega

theorem moved_bound : ContractionBound .right d.C
    (W4.SelectedLogical.rankInnerR d hn Γ f+1) (movedR d hn Γ f)
    (fun a => a.index = 2+d.s.inner.keep.index) := by
  apply UnaryCast.exchangeR_bound [] d.s.I [d.A,d.B] [] (moveSource d) (moveTarget d)
    Γ (W4.SelectedLogical.innerR d hn Γ f) (fun i => i = 2+d.s.inner.keep.index)
  apply (inner_bound d hn Γ f).mono
  intro a ha
  change exchangeIndex 0 d.s.I.length 2 a.index = 2+d.s.inner.keep.index at ha
  have hk := d.s.inner.keep.index_lt
  unfold exchangeIndex at ha
  repeat first | split at ha | omega

theorem head_bound : ContractionBound .right d.C
    (W4.SelectedLogical.rankInnerR d hn Γ f+1) (headR d hn Γ f)
    (fun a => a.index = 0 ∨ a.index = d.s.inner.keep.index+1) := by
  apply ContractionBound.disjR Γ [] d.s.I d.A d.B
  apply (moved_bound d hn Γ f).mono
  rintro a ⟨x,hx,hp⟩
  change At (d.A::d.B::d.s.I) d.C at a
  change At (d.C::d.s.I) d.C at x
  change x.index = 0 ∨ x.index = d.s.inner.keep.index+1 at hx
  change a.index = 2+d.s.inner.keep.index
  have hi := At.fixed_index [] [d.A,d.B] [d.C] d.s.I a
  rw [hp] at hi
  simp only [Option.map_some,List.length_nil,List.length_cons] at hi
  unfold GapLogical.parentIndex at hi
  split at hi
  · omega
  · split at hi
    · cases hi
    · have he : x.index = a.index-2+1 := Option.some.inj hi
      omega

theorem middle_bound : ContractionBound .right d.C
    (W4.SelectedLogical.rankInnerR d hn Γ f+1) (blockedR d hn Γ f)
    (fun a => a.index = d.s.inner.keep.index) := by
  apply (block d).right_bound (Nat.le_refl 2) Γ (headR d hn Γ f)
    (fun i => i = d.s.inner.keep.index) (blocked d hn Γ f)
  apply (head_bound d hn Γ f).mono
  intro a ha
  change copyIndex [[],gaps d.gs] a.index = d.s.inner.keep.index at ha
  rw [ContractionBlock.keep_index] at ha ⊢
  change _ = 0 ∨ _ = (gaps d.gs).length+1
  simp only [copyIndex,gaps,List.length_nil,Nat.not_lt_zero,ite_false,List.append_nil,
    Nat.zero_add] at ha
  repeat first | split at ha | omega

theorem repair_bound : ContractionBound .right d.C
    (W4.SelectedLogical.rankInnerR d hn Γ f+1) (repairR d hn Γ f)
    (fun a => a.index = d.x.index) := by
  apply UnaryCast.exchangeR_bound (gaps d.gs) [d.C] d.Θ []
    d.s.exchangeSource d.s.exchangeTarget Γ (blockedR d hn Γ f) (fun i => i = d.x.index)
  apply (middle_bound d hn Γ f).mono
  intro a ha
  change exchangeIndex (gaps d.gs).length 1 d.Θ.length a.index = d.x.index at ha
  rw [d.s.x_index] at ha
  rw [ContractionBlock.keep_index]
  change exchangeIndex (gaps d.gs).length 1 d.Θ.length a.index =
    (gaps d.gs).length+d.Θ.length at ha
  change a.index = (gaps d.gs).length
  unfold exchangeIndex at ha
  repeat first | split at ha | omega

end DosenPetric.Reduced.Gentzen.W4.HeadRight
