module

public import DosenPetric.GentzenDegreeInduction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace G

/-- Normalize every proof tree at its original sequent, including cuts below rules. -/
theorem cut_free_normalization {Γ Δ : List (NormalForm P)} (t : G P Γ Δ) :
    ∃ h : G P Γ Δ, h.CutFree ∧ ofTerm h.denote = ofTerm t.denote := by
  induction t with
  | identity l => exact ⟨.identity l,rfl,rfl⟩
  | zero l => exact ⟨.zero l,rfl,rfl⟩
  | topI => exact ⟨.topI,rfl,rfl⟩
  | botE => exact ⟨.botE,rfl,rfl⟩
  | exchangeL Γ X Y Θ Δ f ih =>
    obtain ⟨a,ha,ea⟩ := ih
    refine ⟨.exchangeL Γ X Y Θ Δ a,ha,?_⟩
    simp only [denote,ofTerm_comp]
    rw [ea]
  | exchangeR Γ Δ X Y Λ f ih =>
    obtain ⟨a,ha,ea⟩ := ih
    refine ⟨.exchangeR Γ Δ X Y Λ a,ha,?_⟩
    simp only [denote,ofTerm_comp]
    rw [ea]
  | thinL Γ Θ Δ A f ih =>
    obtain ⟨a,ha,ea⟩ := ih
    refine ⟨.thinL Γ Θ Δ A a,ha,?_⟩
    simp only [denote,ofTerm_comp]
    rw [ea]
  | thinR Γ Δ Λ A f ih =>
    obtain ⟨a,ha,ea⟩ := ih
    refine ⟨.thinR Γ Δ Λ A a,ha,?_⟩
    simp only [denote,ofTerm_comp]
    rw [ea]
  | contractL C gs Θ Δ hn f ih =>
    obtain ⟨a,ha,ea⟩ := ih
    refine ⟨.contractL C gs Θ Δ hn a,ha,?_⟩
    simp only [denote,ofTerm_comp]
    rw [ea]
  | contractR Γ C gs Λ hn f ih =>
    obtain ⟨a,ha,ea⟩ := ih
    refine ⟨.contractR Γ C gs Λ hn a,ha,?_⟩
    simp only [denote,ofTerm_comp]
    rw [ea]
  | conjL Γ Θ Δ A B f ih =>
    obtain ⟨a,ha,ea⟩ := ih
    refine ⟨.conjL Γ Θ Δ A B a,ha,?_⟩
    simp only [denote,ofTerm_comp]
    rw [ea]
  | disjR Γ Δ Λ A B f ih =>
    obtain ⟨a,ha,ea⟩ := ih
    refine ⟨.disjR Γ Δ Λ A B a,ha,?_⟩
    simp only [denote,ofTerm_comp]
    rw [ea]
  | conjR f g ih ih' =>
    obtain ⟨a,ha,ea⟩ := ih
    obtain ⟨b,hb,eb⟩ := ih'
    refine ⟨.conjR a b,?_,Rules.conjRight_congr ea eb⟩
    change a.cutCount + b.cutCount = 0
    exact Nat.add_eq_zero_iff.mpr ⟨ha,hb⟩
  | disjL f g ih ih' =>
    obtain ⟨a,ha,ea⟩ := ih
    obtain ⟨b,hb,eb⟩ := ih'
    refine ⟨.disjL a b,?_,Rules.disjLeft_congr ea eb⟩
    change a.cutCount + b.cutCount = 0
    exact Nat.add_eq_zero_iff.mpr ⟨ha,hb⟩
  | mix f g ih ih' =>
    obtain ⟨a,ha,ea⟩ := ih
    obtain ⟨b,hb,eb⟩ := ih'
    refine ⟨.mix a b,?_,Rules.mix_congr ea eb⟩
    change a.cutCount + b.cutCount = 0
    exact Nat.add_eq_zero_iff.mpr ⟨ha,hb⟩
  | @cut Γ Θ Δ Λ C f g ih ih' =>
    obtain ⟨a,ha,ea⟩ := ih
    obtain ⟨b,hb,eb⟩ := ih'
    obtain ⟨h,hh,_,eh⟩ := head_cut_elimination C a b ha hb
    exact ⟨h,hh,eh.trans (Rules.cut_congr ea eb)⟩

end G

/-- The actual unrestricted cut-elimination interface, without supplied handlers. -/
theorem cut_elimination : CutElimination P := G.cut_free_normalization

/-- Simultaneous cut elimination and atomization at the exact original sequent. -/
theorem atomized_cut_elimination : AtomizedCutElimination P := by
  intro Γ Δ t
  obtain ⟨h,hh,eh⟩ := G.cut_free_normalization t
  exact ⟨G.atomize h,G.atomize_cutFree h hh,G.atomize_atomized h,
    (G.atomize_denote h).trans eh⟩

end DosenPetric.Reduced.Gentzen
