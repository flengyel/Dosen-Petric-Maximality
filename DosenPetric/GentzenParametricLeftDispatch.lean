module

public import DosenPetric.GentzenParametricRightDispatch
public import DosenPetric.GentzenBinaryMixRightStep
public import DosenPetric.GentzenConjFirstSelected
public import DosenPetric.GentzenConjRightSecondSelected
public import DosenPetric.GentzenDisjRightFirstSelected
public import DosenPetric.GentzenDisjRightSecondSelected

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.CutCommutation
universe u
variable {P : Type u}

/-- Exhaustive commutation through a parametric antecedent of the right premise.
The recursive cut precedes every reconstruction program. -/
theorem parametric_left_rank_step {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (h : G P Γ Δ) (z : At Δ C) (g : G P Θ Λ) (x : At Θ C)
    (hp : g.Parametric .left x) (hc : PositionalCut.Clean h z g x)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C), PositionalCut.rank b v d w < PositionalCut.rank h z g x →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z g x := by
  cases g with
  | identity => cases hp
  | zero => cases hp
  | topI => cases hp
  | botE => cases hp
  | exchangeL F X Y U Δ g =>
    have hs := StructuralProgram.exchange_singleFiber F X Y U (x.swapBlocks F Y X U)
    rw [At.swapBlocks_inverse] at hs
    exact same_left_rank_step (.exchange F X Y U) (by exact Nat.zero_lt_succ 0) x
      (x.swapBlocks F Y X U) hs h z g hc ih
  | exchangeR Γ F X Y U g =>
    exact selected_opposite_right_rank_step (.exchange F X Y U) (by exact Nat.zero_lt_succ 0) h z g x hc ih
  | thinL F U Δ A g =>
    have hn : x.index ≠ F.length := by
      intro he
      change (if x.index = F.length then 0 else 1) = 1 at hp
      simp only [he,ite_true] at hp
      cases hp
    obtain ⟨a,ha⟩ := thin_old_position F U A x hn
    have hs := StructuralProgram.thin_singleFiber F U A a
    rw [ha] at hs
    exact same_left_rank_step (.thin F U A) (by exact Nat.zero_lt_succ 0) x a hs h z g hc ih
  | thinR Γ F U A g =>
    exact selected_opposite_right_rank_step (.thin F U A) (by exact Nat.zero_lt_succ 0) h z g x hc ih
  | contractL A gs U Δ hn g =>
    have hx : x.index ≠ (gaps gs).length := by
      intro he
      change (if x.index = (gaps gs).length then gs.length else 1) = 1 at hp
      rw [ite_eq_left he] at hp
      omega
    exact same_left_rank_step (.contract A gs U hn) (by exact Nat.zero_lt_succ 0) x
      (fixedCopyAt A gs U x hx) (StructuralProgram.contract_singleFiber A gs U hn x hx)
      h z g hc ih
  | contractR Γ A gs U hn g =>
    exact selected_opposite_right_rank_step (.contract A gs U hn) (by exact Nat.zero_lt_succ 0) h z g x hc ih
  | conjL F U Δ A B g =>
    cases At.cases_append F (.conj A B :: U) x with
    | inl hx =>
      obtain ⟨a,rfl⟩ := hx
      exact same_conjL_before_rank_step h z g a hc ih
    | inr hx =>
      obtain ⟨a,rfl⟩ := hx
      cases a with
      | here =>
        change (if (At.shift F (.here (.conj A B) U)).index = F.length then 0 else 1) = 1 at hp
        simp only [At.index_shift,At.index,Nat.add_zero,ite_true] at hp
        cases hp
      | there a => exact same_conjL_tail_rank_step h z g a hc ih
  | disjR Γ F U A B g => exact opposite_disjR_rank_step h z g x hc ih
  | @conjR Γ Θ Δ Λ A B f g =>
    cases At.cases_append Γ Θ x with
    | inl hx =>
      obtain ⟨a,rfl⟩ := hx
      exact conjR_right_first_rank_step f g h z a hc ih
    | inr hx =>
      obtain ⟨a,rfl⟩ := hx
      exact conjR_right_second_rank_step f g h z a hc ih
  | @disjL Γ Θ Δ Λ A B f g =>
    cases x with
    | here => cases hp
    | there a =>
      cases At.cases_append Γ Θ a with
      | inl ha =>
        obtain ⟨a,rfl⟩ := ha
        exact disjL_right_first_rank_step f g h z a hc ih
      | inr ha =>
        obtain ⟨a,rfl⟩ := ha
        exact disjL_right_second_rank_step f g h z a hc ih
  | @mix Γ Θ Δ Λ f g =>
    cases At.cases_append Θ Γ x with
    | inl hx =>
      obtain ⟨a,rfl⟩ := hx
      exact mix_right_second_rank_step f g h z a hc ih
    | inr hx =>
      obtain ⟨a,rfl⟩ := hx
      exact mix_right_first_rank_step f g h z a hc ih
  | cut f g => exact False.elim (G.cut_not_cutFree f g hc.2.1)

end DosenPetric.Reduced.Gentzen.CutCommutation
