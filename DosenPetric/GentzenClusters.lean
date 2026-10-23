module

public import DosenPetric.GentzenPredecessors
public import DosenPetric.FiniteTraceTree

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- A node keeps its proof occurrence address AND its selected formula position.
    Formula and sequent side are fixed parameters throughout a cluster. -/
structure TraceNode (P : Type u) (s : SequentSide) (C : NormalForm P) where
  source : List (NormalForm P)
  target : List (NormalForm P)
  proof : G P source target
  address : List Nat
  position : Place s source target C

namespace TraceNode
variable {s : SequentSide} {C : NormalForm P}

def descend (n : TraceNode P s C) (a : Upper n.proof s C) : TraceNode P s C :=
  ⟨a.branch.source,a.branch.target,a.branch.proof,n.address ++ [a.branch.occurrence.branch],a.position⟩

/-- Local edges are specified by the independent rule routing. -/
def Edge (n m : TraceNode P s C) : Prop :=
  ∃ a : Upper n.proof s C, n.proof.IsPredecessor s n.position a ∧ n.descend a = m

def next (n : TraceNode P s C) : List (TraceNode P s C) :=
  (n.proof.predecessors s n.position).map n.descend

theorem next_correct (n m : TraceNode P s C) : m ∈ n.next ↔ Edge n m := by
  simp only [next,List.mem_map,Edge]
  constructor
  · rintro ⟨a,ha,hm⟩; exact ⟨a,(n.proof.predecessors_correct s n.position a).mp ha,hm⟩
  · rintro ⟨a,ha,hm⟩; exact ⟨a,(n.proof.predecessors_correct s n.position a).mpr ha,hm⟩

def system (P : Type u) (s : SequentSide) (C : NormalForm P) : FiniteTrace (TraceNode P s C) where
  edge := Edge
  next := next
  next_correct := next_correct
  level n := n.proof.proofSize
  decreases := by
    rintro n m ⟨a,_,rfl⟩
    exact a.branch.occurrence.proofSize_lt

def cluster (n : TraceNode P s C) : TraceTree (TraceNode P s C) := (system P s C).tree n

theorem cluster_root (n : TraceNode P s C) : n.cluster.root = n := (system P s C).tree_root n

theorem cluster_nodes (n m : TraceNode P s C) :
    m ∈ n.cluster.nodes ↔ FiniteTrace.Reach Edge n m := (system P s C).tree_correct n m

/-- Immediate cluster edges are exactly the rule predecessors, in both directions. -/
theorem cluster_children (n m : TraceNode P s C) :
    (∃ t ∈ n.cluster.children, t.root = m) ↔ Edge n m := by
  rw [cluster,FiniteTrace.tree_eq]
  simp only [TraceTree.children,List.mem_map]
  constructor
  · rintro ⟨t,⟨⟨a,ha⟩,_,rfl⟩,hm⟩
    rw [FiniteTrace.tree_root] at hm
    cases hm
    exact (next_correct n a).mp ha
  · intro h
    have hm := (next_correct n m).mpr h
    exact ⟨(system P s C).tree m,⟨⟨m,hm⟩,List.mem_attach _ _,rfl⟩,FiniteTrace.tree_root _ _⟩

theorem cluster_closed {n m k : TraceNode P s C} (hm : m ∈ n.cluster.nodes)
    (hk : Edge m k) : k ∈ n.cluster.nodes := by
  apply (cluster_nodes n k).mpr
  exact ((cluster_nodes n m).mp hm).trans (.step hk (.root k))

def Valid {Γ Δ : List (NormalForm P)} (root : G P Γ Δ) (n : TraceNode P s C) : Prop :=
  ∃ a : ProofAddress root n.proof, a.path = n.address

theorem valid_descend {Γ Δ : List (NormalForm P)} {root : G P Γ Δ}
    {n : TraceNode P s C} (hn : n.Valid root) (a : Upper n.proof s C) :
    (n.descend a).Valid root := by
  obtain ⟨p,hp⟩ := hn
  exact ⟨p.down a.branch.occurrence,congrArg (fun xs => xs ++ [a.branch.occurrence.branch]) hp⟩

theorem reach_valid {Γ Δ : List (NormalForm P)} {root : G P Γ Δ}
    {n m : TraceNode P s C} (h : FiniteTrace.Reach Edge n m) : n.Valid root → m.Valid root := by
  induction h with
  | root => exact fun h => h
  | step he _ ih =>
    rintro hn
    obtain ⟨a,_,rfl⟩ := he
    exact ih (valid_descend hn a)

end TraceNode

namespace G

def traceRoot {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : TraceNode P s C := ⟨Γ,Δ,g,[],x⟩

def cluster {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : TraceTree (TraceNode P s C) := (g.traceRoot s x).cluster

theorem cluster_root {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : (g.cluster s x).root = g.traceRoot s x :=
  TraceNode.cluster_root _

theorem cluster_correct {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) (n : TraceNode P s C) :
    n ∈ (g.cluster s x).nodes ↔ FiniteTrace.Reach TraceNode.Edge (g.traceRoot s x) n :=
  TraceNode.cluster_nodes _ _

theorem cluster_address {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) (n : TraceNode P s C)
    (hn : n ∈ (g.cluster s x).nodes) : n.Valid g :=
  TraceNode.reach_valid ((g.cluster_correct s x n).mp hn) ⟨.root,rfl⟩

end G
end DosenPetric.Reduced.Gentzen
