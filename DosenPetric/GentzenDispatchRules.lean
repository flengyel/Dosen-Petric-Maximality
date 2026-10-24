module

public import DosenPetric.GentzenSelectionDispatch

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace G.RuleKind

def Binary : G.RuleKind → Prop
  | .conjR | .disjL | .mix | .cut => True
  | _ => False

def FreshOn : SequentSide → G.RuleKind → Prop
  | .left,.thinL | .left,.conjL | .left,.disjL => True
  | .right,.thinR | .right,.disjR | .right,.conjR => True
  | _,_ => False
end G.RuleKind

namespace Premise

theorem second_binary {Γ Δ Θ Λ : List (NormalForm P)} {g : G P Γ Δ} {f : G P Θ Λ}
    (p : Premise g f) (hp : p.branch = 1) : g.ruleKind.Binary := by
  cases p <;> simp_all [branch,G.ruleKind,G.RuleKind.Binary]
end Premise

namespace G

theorem fresh_rule {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) (hb : ¬ g.ruleKind.Basis)
    (hx : g.Leaf s x) : g.ruleKind.FreshOn s := by
  cases g <;> cases s <;> simp only [ruleKind,RuleKind.Basis,RuleKind.FreshOn,Leaf,sourceArity] at hb hx ⊢
  all_goals first | exact True.intro | contradiction | omega | (split at hx <;> omega)
end G

namespace PortOrigin
variable {Γ Δ : List (NormalForm P)} {g : G P Γ Δ} {s : SequentSide}
variable {C : NormalForm P} {x : Place s Γ Δ C}

theorem second_binary (h : PortOrigin g s x .second) : g.ruleKind.Binary := by
  cases h with | second a _ hb => exact a.branch.occurrence.second_binary hb

theorem shared_rule (h : PortOrigin g s x .shared) :
    match s with
    | .left => g.ruleKind = .contractL
    | .right => g.ruleKind = .contractR := by
  cases h with | shared h => cases h <;> rfl

theorem fresh_rule (h : PortOrigin g s x .fresh) (hb : ¬ g.ruleKind.Basis) :
    g.ruleKind.FreshOn s := g.fresh_rule s x hb h.arity
end PortOrigin

namespace G
variable {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide) {C : NormalForm P}

theorem port_member (xs : List (Place s Γ Δ C)) (p : SelectionPort) :
    p ∈ g.selectionPorts s xs ↔ ∃ x, x ∈ xs ∧ PortOrigin g s x p := by
  constructor
  · intro hp
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hp
    exact ⟨x,hx,he ▸ g.selectionPort_spec s x⟩
  · rintro ⟨x,hx,hp⟩
    have he := (g.selectionPort_spec s x).unique hp
    exact List.mem_map.mpr ⟨x,hx,he⟩

theorem selected_second_binary (xs : List (Place s Γ Δ C))
    (hs : .second ∈ g.selectionPorts s xs) : g.ruleKind.Binary := by
  obtain ⟨_,_,h⟩ := (g.port_member s xs .second).mp hs
  exact h.second_binary

theorem selected_shared_rule (xs : List (Place s Γ Δ C))
    (hs : .shared ∈ g.selectionPorts s xs) :
    match s with
    | .left => g.ruleKind = .contractL
    | .right => g.ruleKind = .contractR := by
  obtain ⟨_,_,h⟩ := (g.port_member s xs .shared).mp hs
  cases s <;> exact h.shared_rule

theorem selected_fresh_rule (xs : List (Place s Γ Δ C))
    (hb : ¬ g.ruleKind.Basis) (hs : .fresh ∈ g.selectionPorts s xs) : g.ruleKind.FreshOn s := by
  obtain ⟨_,_,h⟩ := (g.port_member s xs .fresh).mp hs
  exact h.fresh_rule hb

end G
end DosenPetric.Reduced.Gentzen
