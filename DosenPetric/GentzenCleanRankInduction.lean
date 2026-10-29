module

public import DosenPetric.GentzenParametricLeftDispatch
public import DosenPetric.GentzenRankTwoDegreeStep
public import DosenPetric.GentzenSelectedCleanCuts

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.PositionalCut
universe u
variable {P : Type u}

/-- The complete selected-position dispatch under the strict outer degree hypothesis. -/
theorem clean_rank_step {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (hd : DegreeBelow P (cutDegree C))
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hc : Clean f x g y)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C), rank b v d w < rank f x g y →
      Clean b v d w → Eliminated b v d w) : Eliminated f x g y := by
  cases f.position_classification .right x with
  | inr hf => cases hf with
    | inl hp => exact CutCommutation.parametric_right_rank_step f x g y hp hc ih
    | inr hl =>
      have hb : BlockedR f := hc.2.2.2.2.1 .root x rfl hl
      exact CutCommutation.blocked_right_rank_step f x g y hb hl hc ih
  | inl hf =>
    cases g.position_classification .left y with
    | inr hg => cases hg with
      | inl hp => exact CutCommutation.parametric_left_rank_step f x g y hp hc ih
      | inr hl =>
        have hb : BlockedL g := hc.2.2.2.2.2 .root y rfl hl
        exact CutCommutation.blocked_left_rank_step f x g y hb hl hc ih
    | inl hg =>
      exact rank_two_degree_step hd f x g y hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1
        ((rank_two_iff_leaves f x g y).mpr ⟨hf,hg⟩)

/-- At one fixed degree, eliminate every clean cut by its original selected rank. -/
theorem clean_elimination {C : NormalForm P} (hd : DegreeBelow P (cutDegree C))
    {Γ Δ Θ Λ : List (NormalForm P)}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hc : Clean f x g y) : Eliminated f x g y := by
  have hall : ∀ n : Nat, ∀ {K L M N : List (NormalForm P)}
      (b : G P K L) (v : At L C) (d : G P M N) (w : At M C),
      rank b v d w = n → Clean b v d w → Eliminated b v d w := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro K L M N b v d w he hc'
      apply clean_rank_step hd b v d w hc'
      intro I J U V a z e t hr ha
      apply ih (rank a z e t) (by rw [← he]; exact hr) a z e t rfl ha
  exact hall (rank f x g y) f x g y rfl hc

/-- Cleaning is used only after all original ranks at this degree have been discharged. -/
theorem cutFree_degree_step {C : NormalForm P} (hd : DegreeBelow P (cutDegree C))
    {Γ Δ Θ Λ : List (NormalForm P)}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hf : f.CutFree) (hg : g.CutFree) : Eliminated f x g y := by
  obtain ⟨f',g',hc,ef,eg⟩ := clean_premises f x g y hf hg
  obtain ⟨h,hh,ah,eh⟩ := clean_elimination hd f' x g' y hc
  exact ⟨h,hh,ah,eh.trans (congr x y ef eg)⟩

end DosenPetric.Reduced.Gentzen.PositionalCut
