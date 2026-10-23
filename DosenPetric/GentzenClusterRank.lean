module

public import DosenPetric.GentzenClusters

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace TraceNode
variable {s : SequentSide} {C : NormalForm P}

def rank (n : TraceNode P s C) : Nat := (system P s C).rank n

theorem rank_eq (n : TraceNode P s C) :
    n.rank = 1 + ((n.proof.predecessors s n.position).map (fun a => (n.descend a).rank)).sum := by
  rw [rank,FiniteTrace.rank_eq]
  simp only [system,next,List.map_map]
  rfl

theorem rank_readdress {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) (a b : List Nat) :
    (TraceNode.mk Γ Δ g a x).rank = (TraceNode.mk Γ Δ g b x).rank := by
  rw [rank_eq (TraceNode.mk Γ Δ g a x),rank_eq (TraceNode.mk Γ Δ g b x)]
  apply congrArg (fun n => 1+n)
  apply congrArg List.sum
  apply List.map_congr_left
  intro v _
  exact rank_readdress v.branch.proof s v.position
    (a ++ [v.branch.occurrence.branch]) (b ++ [v.branch.occurrence.branch])
termination_by g.proofSize
decreasing_by exact v.branch.occurrence.proofSize_lt

end TraceNode

namespace G

/-- Total cluster-node count, attached to this syntactic proof and position. -/
def rho {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : Nat := (g.traceRoot s x).rank

theorem rho_counts_nodes {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : g.rho s x = (g.cluster s x).count := rfl

theorem rho_eq {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) :
    g.rho s x = 1 + ((g.predecessors s x).map (fun a => a.branch.proof.rho s a.position)).sum := by
  rw [rho,TraceNode.rank_eq]
  apply congrArg (fun n => 1+n)
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  exact TraceNode.rank_readdress a.branch.proof s a.position [a.branch.occurrence.branch] []

theorem rho_pos {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : 0 < g.rho s x := FiniteTrace.rank_pos _ _

theorem rho_child_lt {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) (a : Upper g s C)
    (ha : g.IsPredecessor s x a) : a.branch.proof.rho s a.position < g.rho s x := by
  have h := nat_le_map_sum (fun a : Upper g s C => a.branch.proof.rho s a.position)
    ((g.predecessors_correct s x a).mpr ha)
  rw [rho_eq g s x]
  omega

theorem rho_one_iff {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) :
    g.rho s x = 1 ↔ ∀ a : Upper g s C, ¬ g.IsPredecessor s x a := by
  rw [rho,TraceNode.rank,FiniteTrace.rank_one_iff]
  constructor
  · intro h a ha
    have hm : (g.traceRoot s x).descend a ∈ (g.traceRoot s x).next :=
      List.mem_map.mpr ⟨a,(g.predecessors_correct s x a).mpr ha,rfl⟩
    change (g.traceRoot s x).next = [] at h
    rw [h] at hm
    cases hm
  · intro h
    change (g.traceRoot s x).next = []
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro n hn
    obtain ⟨a,ha,_⟩ := List.mem_map.mp hn
    exact h a ((g.predecessors_correct s x a).mp ha)

def leftCutRank {Γ Δ : List (NormalForm P)} {C : NormalForm P} (f : G P Γ (C :: Δ)) : Nat :=
  f.rho .right (.here C Δ)

def rightCutRank {Θ Λ : List (NormalForm P)} {C : NormalForm P} (g : G P (C :: Θ) Λ) : Nat :=
  g.rho .left (.here C Θ)

def cutRank {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) : Nat := f.leftCutRank + g.rightCutRank

theorem cutRank_ge_two {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) : 2 ≤ cutRank f g := by
  have h₁ := rho_pos f .right (.here C Δ)
  have h₂ := rho_pos g .left (.here C Θ)
  change 2 ≤ f.rho .right (.here C Δ) + g.rho .left (.here C Θ)
  omega

theorem cutRank_eq_two {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) :
    cutRank f g = 2 ↔ f.leftCutRank = 1 ∧ g.rightCutRank = 1 := by
  have h₁ := rho_pos f .right (.here C Δ)
  have h₂ := rho_pos g .left (.here C Θ)
  change f.leftCutRank > 0 at h₁
  change g.rightCutRank > 0 at h₂
  unfold cutRank
  omega

def contractionRankL (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Δ : List (NormalForm P)) (hn : 2 ≤ gs.length) (f : G P (repeated C gs ++ Θ) Δ) : Nat :=
  (G.contractL C gs Θ Δ hn f).rho .left (At.shift (gaps gs) (.here C Θ))

def contractionRankR (Γ : List (NormalForm P)) (C : NormalForm P)
    (gs : List (List (NormalForm P))) (Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (f : G P Γ (repeated C gs ++ Λ)) : Nat :=
  (G.contractR Γ C gs Λ hn f).rho .right (At.shift (gaps gs) (.here C Λ))

end G
end DosenPetric.Reduced.Gentzen
