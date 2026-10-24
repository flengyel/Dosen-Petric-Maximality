module

public import DosenPetric.GentzenSelectionOrigins

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- The first applicable shared/introduced/parametric regime, with premise tags. -/
inductive SelectionRegime where
  | shared | selectedFirst | selectedSecond | selectedBoth
  | parametricFirst | parametricSecond | parametricBoth
  deriving DecidableEq

namespace SelectionRegime

def Holds (ps : List SelectionPort) : SelectionRegime → Prop
  | .shared => .shared ∈ ps
  | .selectedFirst => .shared ∉ ps ∧ .fresh ∈ ps ∧ .first ∈ ps ∧ .second ∉ ps
  | .selectedSecond => .shared ∉ ps ∧ .fresh ∈ ps ∧ .first ∉ ps ∧ .second ∈ ps
  | .selectedBoth => .shared ∉ ps ∧ .fresh ∈ ps ∧ .first ∈ ps ∧ .second ∈ ps
  | .parametricFirst => .shared ∉ ps ∧ .fresh ∉ ps ∧ .first ∈ ps ∧ .second ∉ ps
  | .parametricSecond => .shared ∉ ps ∧ .fresh ∉ ps ∧ .first ∉ ps ∧ .second ∈ ps
  | .parametricBoth => .shared ∉ ps ∧ .fresh ∉ ps ∧ .first ∈ ps ∧ .second ∈ ps

theorem classify (ps : List SelectionPort)
    (hp : .shared ∉ ps → .first ∈ ps ∨ .second ∈ ps) : ∃ r : SelectionRegime, r.Holds ps := by
  by_cases hs : .shared ∈ ps
  · exact ⟨.shared,hs⟩
  · have hb := hp hs
    by_cases hf : .fresh ∈ ps <;> by_cases h₀ : .first ∈ ps <;> by_cases h₁ : .second ∈ ps
    · exact ⟨.selectedBoth,hs,hf,h₀,h₁⟩
    · exact ⟨.selectedFirst,hs,hf,h₀,h₁⟩
    · exact ⟨.selectedSecond,hs,hf,h₀,h₁⟩
    · exact False.elim (hb.elim h₀ h₁)
    · exact ⟨.parametricBoth,hs,hf,h₀,h₁⟩
    · exact ⟨.parametricFirst,hs,hf,h₀,h₁⟩
    · exact ⟨.parametricSecond,hs,hf,h₀,h₁⟩
    · exact False.elim (hb.elim h₀ h₁)

theorem unique (ps : List SelectionPort) (r q : SelectionRegime)
    (hr : r.Holds ps) (hq : q.Holds ps) : r = q := by
  cases r <;> cases q <;> simp_all [Holds]

end SelectionRegime

namespace G
variable {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide) {C : NormalForm P}

noncomputable def selectionPorts (xs : List (Place s Γ Δ C)) : List SelectionPort := xs.map (g.selectionPort s)

theorem ports_complete (xs : List (Place s Γ Δ C)) :
    ∀ x ∈ xs, PortOrigin g s x (g.selectionPort s x) := by
  intro x _
  exact g.selectionPort_spec s x

theorem ports_branch_exists (xs : List (Place s Γ Δ C))
    (hp : ∃ a b, a ∈ xs ∧ b ∈ xs ∧ a.index < b.index)
    (hs : .shared ∉ g.selectionPorts s xs) :
    .first ∈ g.selectionPorts s xs ∨ .second ∈ g.selectionPorts s xs := by
  classical
  apply Classical.byContradiction
  intro hb
  have h₀ : .first ∉ g.selectionPorts s xs := fun h => hb (.inl h)
  have h₁ : .second ∉ g.selectionPorts s xs := fun h => hb (.inr h)
  have fresh : ∀ x ∈ xs, g.Leaf s x := by
    intro x hx
    have hm : g.selectionPort s x ∈ g.selectionPorts s xs := List.mem_map_of_mem hx
    have ho := g.selectionPort_spec s x
    cases he : g.selectionPort s x <;> rw [he] at hm ho
    · exact ho.arity
    · exact False.elim (h₀ hm)
    · exact False.elim (h₁ hm)
    · exact False.elim (hs hm)
  obtain ⟨a,b,ha,hb,hab⟩ := hp
  have he := g.leaf_indices s a b (fresh a ha) (fresh b hb)
  omega

theorem selection_classification (xs : List (Place s Γ Δ C))
    (hp : ∃ a b, a ∈ xs ∧ b ∈ xs ∧ a.index < b.index) :
    ∃ r : SelectionRegime, r.Holds (g.selectionPorts s xs) :=
  SelectionRegime.classify _ (g.ports_branch_exists s xs hp)

end G

namespace ContractionBlock
variable {U K : List (NormalForm P)} (d : ContractionBlock P U K) (hn : 2 ≤ d.gs.length)
include hn

theorem classificationL {Δ : List (NormalForm P)} (g : G P U Δ) (hg : g.CutFree) :
    ¬ g.ruleKind.Basis ∧ g.ruleKind ≠ .cut ∧
      ∃ r : SelectionRegime, r.Holds (g.selectionPorts .left d.selected) :=
  ⟨d.not_basisL hn g,g.cutFree_not_cut hg,g.selection_classification .left _ (d.selected_pair hn)⟩

theorem classificationR {Γ : List (NormalForm P)} (g : G P Γ U) (hg : g.CutFree) :
    ¬ g.ruleKind.Basis ∧ g.ruleKind ≠ .cut ∧
      ∃ r : SelectionRegime, r.Holds (g.selectionPorts .right d.selected) :=
  ⟨d.not_basisR hn g,g.cutFree_not_cut hg,g.selection_classification .right _ (d.selected_pair hn)⟩

end ContractionBlock
end DosenPetric.Reduced.Gentzen
