module

public import DosenPetric.GentzenReducibilityObstructions
public import DosenPetric.GentzenSelectedLogicalExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.RightLogicalRegression

abbrev C : NormalForm Empty := .disj .bot .bot
abbrev data := W4.SelectedLogical.Examples.two .disj (.bot : NormalForm Empty) .bot
abbrev premise := W4.SelectedLogical.Examples.constRight data
abbrev other := BlockedExamples.l [C]
abbrev old : G Empty [.bot] [C] := W4.SelectedLogical.oldR data (Nat.le_refl 2) [.bot] premise
abbrev terminal : G Empty [.bot] [C] := W4.SelectedLogical.newR data (Nat.le_refl 2) [.bot] premise

theorem premise_cutFree : premise.CutFree := G.atomize_cutFree _ rfl
theorem other_cutFree : other.CutFree := G.atomize_cutFree _ rfl
theorem old_cutFree : old.CutFree :=
  (W4.SelectedLogical.old_cutFreeR data (Nat.le_refl 2) [.bot] premise).mpr premise_cutFree
theorem terminal_cutFree : terminal.CutFree :=
  (W4.SelectedLogical.new_cutFreeR data (Nat.le_refl 2) [.bot] premise).mpr premise_cutFree

theorem old_unblocked : ¬ BlockedR old := by
  intro hb
  have h := hb.disjRightPrefix
  change some 2 ∈ [none,some 0] at h
  have hn : some 2 ∉ ([none,some 0] : List (Option Nat)) := by decide
  exact hn h

theorem terminal_unblocked : ¬ BlockedR terminal :=
  ReducibilityObstructions.terminal_right_w4_unblocked data (Nat.le_refl 2) [.bot] premise

theorem old_reducible : ReducibleR old other ProofAddress.root (.here C []) := by
  refine ⟨⟨old_cutFree,other_cutFree⟩,?_,old_unblocked,?_⟩
  · exact ⟨((ProofAddress.root : ProofAddress old old).cluster_iff_ascend .right _ _).mpr rfl,
      G.LowerContraction.right ..⟩
  · intro I J v b y _ hba
    have h := ProofAddress.proper_length hba
    change b.path.length < 0 at h
    omega

theorem terminal_reducible : ReducibleR terminal other ProofAddress.root (.here C []) := by
  refine ⟨⟨terminal_cutFree,other_cutFree⟩,?_,terminal_unblocked,?_⟩
  · exact ⟨((ProofAddress.root : ProofAddress terminal terminal).cluster_iff_ascend .right _ _).mpr rfl,
      G.LowerContraction.right ..⟩
  · intro I J v b y _ hba
    have h := ProofAddress.proper_length hba
    change b.path.length < 0 at h
    omega

theorem equal_retained_rank : terminal.rho .right (.here C []) = old.rho .right (.here C []) :=
  W4.SelectedLogical.endpoint_tieR data (Nat.le_refl 2) [.bot] premise rfl

/-- A counterexample to the terminal candidate, not to existential Reducibility. -/
theorem terminal_fails_strict_target : ¬
    (∀ {I J : List (NormalForm Empty)} {v : G Empty I J}
      (b : ProofAddress terminal v) (y : At J C),
      ReducibleR terminal other b y → v.rho .right y < old.rho .right (.here C [])) := by
  intro h
  have hr := h ProofAddress.root (.here C []) terminal_reducible
  rw [equal_retained_rank] at hr
  omega

end DosenPetric.Reduced.Gentzen.RightLogicalRegression
