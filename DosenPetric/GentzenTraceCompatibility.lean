module

public import DosenPetric.GentzenClassifiedRank

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace Premise

theorem cutFree {Γ Δ Θ Λ : List (NormalForm P)} {f : G P Γ Δ} {g : G P Θ Λ}
    (p : Premise f g) (h : f.CutFree) : g.CutFree := by
  cases p <;> simp only [G.CutFree,G.cutCount] at h ⊢ <;> omega

theorem atomized {Γ Δ Θ Λ : List (NormalForm P)} {f : G P Γ Δ} {g : G P Θ Λ}
    (p : Premise f g) (h : f.Atomized) : g.Atomized := by
  cases p <;> simp only [G.Atomized] at h ⊢
  all_goals first | exact h | exact h.1 | exact h.2

end Premise

namespace ProofAddress

theorem cutFree {Γ Δ Θ Λ : List (NormalForm P)} {root : G P Γ Δ} {g : G P Θ Λ}
    (a : ProofAddress root g) (h : root.CutFree) : g.CutFree := by
  induction a with
  | root => exact h
  | down _ p ih => exact p.cutFree ih

theorem atomized {Γ Δ Θ Λ : List (NormalForm P)} {root : G P Γ Δ} {g : G P Θ Λ}
    (a : ProofAddress root g) (h : root.Atomized) : g.Atomized := by
  induction a with
  | root => exact h
  | down _ p ih => exact p.atomized ih

end ProofAddress

namespace Place

def reindex {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    {s : SequentSide} {C : NormalForm P} (x : Place s Γ Δ C) : Place s Γ' Δ' C :=
  hΓ ▸ hΔ ▸ x

end Place

namespace Upper

def reindex {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    {g : G P Γ Δ} {s : SequentSide} {C : NormalForm P} (a : Upper g s C) :
    Upper (g.reindex hΓ hΔ) s C := by
  cases hΓ; cases hΔ; exact a

end Upper

namespace G

theorem predecessors_reindex {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (g : G P Γ Δ) (s : SequentSide) {C : NormalForm P} (x : Place s Γ Δ C) :
    (g.reindex hΓ hΔ).predecessors s (Place.reindex hΓ hΔ x) =
      (g.predecessors s x).map (Upper.reindex hΓ hΔ) := by
  cases hΓ; cases hΔ
  change g.predecessors s x = (g.predecessors s x).map (fun a => a)
  simp

theorem cluster_reindex {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (g : G P Γ Δ) (s : SequentSide) {C : NormalForm P} (x : Place s Γ Δ C) :
    (g.reindex hΓ hΔ).cluster s (Place.reindex hΓ hΔ x) = g.cluster s x := by
  cases hΓ; cases hΔ; rfl

theorem rho_reindex {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (g : G P Γ Δ) (s : SequentSide) {C : NormalForm P} (x : Place s Γ Δ C) :
    (g.reindex hΓ hΔ).rho s (Place.reindex hΓ hΔ x) = g.rho s x := by
  cases hΓ; cases hΔ; rfl

theorem rho_node_list {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : g.rho s x = (g.cluster s x).nodes.length :=
  (g.rho_counts_nodes s x).trans (TraceTree.count_nodes _)

theorem cluster_cutFree {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) (hg : g.CutFree)
    (n : TraceNode P s C) (hn : n ∈ (g.cluster s x).nodes) : n.proof.CutFree := by
  obtain ⟨a,_⟩ := g.cluster_address s x n hn
  exact a.cutFree hg

theorem cluster_atomized {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) (hg : g.Atomized)
    (n : TraceNode P s C) (hn : n ∈ (g.cluster s x).nodes) : n.proof.Atomized := by
  obtain ⟨a,_⟩ := g.cluster_address s x n hn
  exact a.atomized hg

/-- A tied left contraction in the right cut-premise, without a cut-free hypothesis. -/
def TiedRight {Θ Λ : List (NormalForm P)} {C : NormalForm P} (g : G P (C :: Θ) Λ)
    (n : TraceNode P .left C) : Prop :=
  n ∈ (g.cluster .left (.here C Θ)).nodes ∧ LowerContraction n.proof .left n.position

def TiedLeft {Γ Δ : List (NormalForm P)} {C : NormalForm P} (f : G P Γ (C :: Δ))
    (n : TraceNode P .right C) : Prop :=
  n ∈ (f.cluster .right (.here C Δ)).nodes ∧ LowerContraction n.proof .right n.position

theorem tiedRight_iff_branching {Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (g : G P (C :: Θ) Λ) (n : TraceNode P .left C) :
    g.TiedRight n ↔ n ∈ (g.cluster .left (.here C Θ)).nodes ∧
      2 ≤ (n.proof.predecessors .left n.position).length := by
  exact and_congr Iff.rfl ((n.proof.lowerContraction_iff_arity .left n.position).trans
    (congrArg (fun k => 2 ≤ k) (n.proof.sourceArity_correct .left n.position)).symm.to_iff)

theorem tiedLeft_iff_branching {Γ Δ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ (C :: Δ)) (n : TraceNode P .right C) :
    f.TiedLeft n ↔ n ∈ (f.cluster .right (.here C Δ)).nodes ∧
      2 ≤ (n.proof.predecessors .right n.position).length := by
  exact and_congr Iff.rfl ((n.proof.lowerContraction_iff_arity .right n.position).trans
    (congrArg (fun k => 2 ≤ k) (n.proof.sourceArity_correct .right n.position)).symm.to_iff)

end G
end DosenPetric.Reduced.Gentzen
