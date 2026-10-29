module

public import DosenPetric.GentzenBlockedLeftRankDispatch
public import DosenPetric.GentzenOppositeStructuralReplacement
public import DosenPetric.GentzenOppositeLogicalDescent
public import DosenPetric.GentzenStructuralSingleFibers
public import DosenPetric.GentzenStructuralCutDescent
public import DosenPetric.GentzenBinaryMixLeftStep
public import DosenPetric.GentzenConjLeftSelected
public import DosenPetric.GentzenConjSecondSelected
public import DosenPetric.GentzenDisjFirstSelected
public import DosenPetric.GentzenDisjSecondSelected

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.CutCommutation
universe u
variable {P : Type u}

/-- Exhaustive commutation through a parametric succedent of the left premise.
Every recursive call uses the original child and the unchanged right premise. -/
theorem parametric_right_rank_step {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hp : f.Parametric .right x) (hc : PositionalCut.Clean f x g y)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C), PositionalCut.rank b v d w < PositionalCut.rank f x g y →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated f x g y := by
  cases f with
  | identity => cases hp
  | zero => cases hp
  | topI => cases hp
  | botE => cases hp
  | exchangeL F X Y U Δ f =>
    exact selected_opposite_left_rank_step (.exchange F X Y U) (by exact Nat.zero_lt_succ 0) f x g y hc ih
  | exchangeR Γ F X Y U f =>
    have hs := StructuralProgram.exchange_singleFiber F X Y U (x.swapBlocks F Y X U)
    rw [At.swapBlocks_inverse] at hs
    exact same_right_rank_step (.exchange F X Y U) (by exact Nat.zero_lt_succ 0) x
      (x.swapBlocks F Y X U) hs f g y hc ih
  | thinL F U Δ A f =>
    exact selected_opposite_left_rank_step (.thin F U A) (by exact Nat.zero_lt_succ 0) f x g y hc ih
  | thinR Γ F U A f =>
    have hn : x.index ≠ F.length := by
      intro he
      change (if x.index = F.length then 0 else 1) = 1 at hp
      simp only [he,ite_true] at hp
      cases hp
    obtain ⟨a,ha⟩ := thin_old_position F U A x hn
    have hs := StructuralProgram.thin_singleFiber F U A a
    rw [ha] at hs
    exact same_right_rank_step (.thin F U A) (by exact Nat.zero_lt_succ 0) x a hs f g y hc ih
  | contractL A gs U Δ hn f =>
    exact selected_opposite_left_rank_step (.contract A gs U hn) (by exact Nat.zero_lt_succ 0) f x g y hc ih
  | contractR Γ A gs U hn f =>
    have hx : x.index ≠ (gaps gs).length := by
      intro he
      change (if x.index = (gaps gs).length then gs.length else 1) = 1 at hp
      rw [ite_eq_left he] at hp
      omega
    exact same_right_rank_step (.contract A gs U hn) (by exact Nat.zero_lt_succ 0) x
      (fixedCopyAt A gs U x hx) (StructuralProgram.contract_singleFiber A gs U hn x hx)
      f g y hc ih
  | conjL F U Δ A B f => exact opposite_conjL_rank_step f x g y hc ih
  | disjR Γ F U A B f =>
    cases At.cases_append F (.disj A B :: U) x with
    | inl hx =>
      obtain ⟨a,rfl⟩ := hx
      exact same_disjR_before_rank_step f a g y hc ih
    | inr hx =>
      obtain ⟨a,rfl⟩ := hx
      cases a with
      | here =>
        change (if (At.shift F (.here (.disj A B) U)).index = F.length then 0 else 1) = 1 at hp
        simp only [At.index_shift,At.index,Nat.add_zero,ite_true] at hp
        cases hp
      | there a => exact same_disjR_tail_rank_step f a g y hc ih
  | @conjR Γ Θ Δ Λ A B f h =>
    cases x with
    | here => cases hp
    | there a =>
      cases At.cases_append Δ Λ a with
      | inl ha =>
        obtain ⟨a,rfl⟩ := ha
        exact conjR_left_first_rank_step f h a g y hc ih
      | inr ha =>
        obtain ⟨a,rfl⟩ := ha
        exact conjR_left_second_rank_step f h a g y hc ih
  | @disjL Γ Θ Δ Λ A B f h =>
    cases At.cases_append Δ Λ x with
    | inl hx =>
      obtain ⟨a,rfl⟩ := hx
      exact disjL_left_first_rank_step f h a g y hc ih
    | inr hx =>
      obtain ⟨a,rfl⟩ := hx
      exact disjL_left_second_rank_step f h a g y hc ih
  | @mix Γ Θ Δ Λ f h =>
    cases At.cases_append Λ Δ x with
    | inl hx =>
      obtain ⟨a,rfl⟩ := hx
      exact mix_left_second_rank_step f h a g y hc ih
    | inr hx =>
      obtain ⟨a,rfl⟩ := hx
      exact mix_left_first_rank_step f h a g y hc ih
  | cut f h => exact False.elim (G.cut_not_cutFree f h hc.1)

end DosenPetric.Reduced.Gentzen.CutCommutation
