module

public import DosenPetric.GentzenProofReplacement
public import DosenPetric.GentzenContractionSelectionCoordinates

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace Premise
theorem branch_zero_or_one {Γ Δ Θ Λ : List (NormalForm P)} {f : G P Γ Δ} {g : G P Θ Λ}
    (p : Premise f g) : p.branch = 0 ∨ p.branch = 1 := by cases p <;> first | exact Or.inl rfl | exact Or.inr rfl
end Premise

namespace G

theorem leaf_indices {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x y : Place s Γ Δ C) (hx : g.Leaf s x) (hy : g.Leaf s y) :
    x.index = y.index := by
  have hi := x.index_lt
  have hj := y.index_lt
  cases g <;> cases s <;> simp only [Leaf,sourceArity] at hx hy
  all_goals simp only [SequentSide.context,List.length_cons,List.length_nil] at hi hj
  all_goals try exact (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi)).trans (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)).symm
  all_goals try omega
  all_goals split at hx <;> split at hy <;> omega

inductive RuleKind where
  | identity | zero | topI | botE | exchangeL | exchangeR | thinL | thinR
  | contractL | contractR | conjL | disjR | conjR | disjL | mix | cut
  deriving DecidableEq

def ruleKind : {Γ Δ : List (NormalForm P)} → G P Γ Δ → RuleKind
  | _,_,.identity _ => .identity
  | _,_,.zero _ => .zero
  | _,_,.topI => .topI
  | _,_,.botE => .botE
  | _,_,.exchangeL .. => .exchangeL
  | _,_,.exchangeR .. => .exchangeR
  | _,_,.thinL .. => .thinL
  | _,_,.thinR .. => .thinR
  | _,_,.contractL .. => .contractL
  | _,_,.contractR .. => .contractR
  | _,_,.conjL .. => .conjL
  | _,_,.disjR .. => .disjR
  | _,_,.conjR .. => .conjR
  | _,_,.disjL .. => .disjL
  | _,_,.mix .. => .mix
  | _,_,.cut .. => .cut

def RuleKind.Basis : RuleKind → Prop
  | .identity | .zero | .topI | .botE => True
  | _ => False

theorem cutFree_not_cut {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (hg : g.CutFree) :
    g.ruleKind ≠ .cut := by
  cases g <;> simp only [ruleKind]
  all_goals first | decide | exact False.elim (cut_not_cutFree _ _ hg)

end G

inductive SelectionPort where
  | fresh | first | second | shared
  deriving DecidableEq

/-- A port carries complete predecessor data, not a test on formula labels. -/
inductive PortOrigin {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : SelectionPort → Prop where
  | fresh : g.Leaf s x → PortOrigin g s x .fresh
  | first (a : Upper g s C) : g.predecessors s x = [a] →
      a.branch.occurrence.branch = 0 → PortOrigin g s x .first
  | second (a : Upper g s C) : g.predecessors s x = [a] →
      a.branch.occurrence.branch = 1 → PortOrigin g s x .second
  | shared : G.LowerContraction g s x → PortOrigin g s x .shared

namespace G

theorem port_exists {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : ∃ p, PortOrigin g s x p := by
  cases g.position_classification s x with
  | inl h => exact ⟨.fresh,.fresh h⟩
  | inr h =>
    cases h with
    | inr h => exact ⟨.shared,.shared h⟩
    | inl h =>
      obtain ⟨a,ha,_⟩ := g.parametric_unique s x h
      cases a.branch.occurrence.branch_zero_or_one with
      | inl hb => exact ⟨.first,.first a ha hb⟩
      | inr hb => exact ⟨.second,.second a ha hb⟩

noncomputable def selectionPort {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : SelectionPort := Classical.choose (g.port_exists s x)

theorem selectionPort_spec {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : PortOrigin g s x (g.selectionPort s x) :=
  Classical.choose_spec (g.port_exists s x)

end G

namespace PortOrigin
variable {Γ Δ : List (NormalForm P)} {g : G P Γ Δ} {s : SequentSide} {C : NormalForm P}
variable {x : Place s Γ Δ C} {p : SelectionPort}

theorem arity (h : PortOrigin g s x p) :
    match p with
    | .fresh => g.sourceArity s x = 0
    | .first | .second => g.sourceArity s x = 1
    | .shared => 2 ≤ g.sourceArity s x := by
  cases h with
  | fresh h => exact h
  | first a ha _ => exact (g.sourceArity_correct s x).symm.trans (congrArg List.length ha)
  | second a ha _ => exact (g.sourceArity_correct s x).symm.trans (congrArg List.length ha)
  | shared h => exact (g.lowerContraction_iff_arity s x).mp h

theorem unique {q : SelectionPort} (h : PortOrigin g s x p) (k : PortOrigin g s x q) : p = q := by
  have hp := h.arity
  have hq := k.arity
  cases h <;> cases k <;> first
    | rfl
    | omega
    | rename_i a ha hb b hc hd
      have he := List.cons.inj (ha.symm.trans hc)
      cases he.1
      omega

end PortOrigin

namespace G
theorem selectionPort_eq {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) (p : SelectionPort) (h : PortOrigin g s x p) :
    g.selectionPort s x = p := (g.selectionPort_spec s x).unique h
end G

namespace ContractionBlock
variable {U K : List (NormalForm P)} (d : ContractionBlock P U K)

theorem selected_pair (hn : 2 ≤ d.gs.length) :
    ∃ a b, a ∈ d.selected ∧ b ∈ d.selected ∧ a.index < b.index := by
  have hl := d.selected_length
  have ho := d.selected_ordered
  cases he : d.selected with
  | nil => rw [he] at hl; simp only [List.length_nil] at hl; omega
  | cons a as =>
    cases as with
    | nil => rw [he] at hl; simp only [List.length_cons,List.length_nil] at hl; omega
    | cons b bs =>
      rw [he] at ho
      exact ⟨a,b,List.mem_cons_self,
        List.mem_cons_of_mem _ List.mem_cons_self,
        (List.pairwise_cons.mp ho).1 b List.mem_cons_self⟩

theorem not_basisL (hn : 2 ≤ d.gs.length) {Δ : List (NormalForm P)} (g : G P U Δ) :
    ¬ g.ruleKind.Basis := by
  obtain ⟨a,b,_,_,hab⟩ := d.selected_pair hn
  have hi := a.index_lt
  have hj := b.index_lt
  intro hb
  cases g <;> simp only [G.ruleKind,G.RuleKind.Basis] at hb
  all_goals try contradiction
  all_goals simp only [List.length_cons,List.length_nil] at hi hj
  all_goals omega

theorem not_basisR (hn : 2 ≤ d.gs.length) {Γ : List (NormalForm P)} (g : G P Γ U) :
    ¬ g.ruleKind.Basis := by
  obtain ⟨a,b,_,_,hab⟩ := d.selected_pair hn
  have hi := a.index_lt
  have hj := b.index_lt
  intro hb
  cases g <;> simp only [G.ruleKind,G.RuleKind.Basis] at hb
  all_goals try contradiction
  all_goals simp only [List.length_cons,List.length_nil] at hi hj
  all_goals omega

end ContractionBlock
end DosenPetric.Reduced.Gentzen
