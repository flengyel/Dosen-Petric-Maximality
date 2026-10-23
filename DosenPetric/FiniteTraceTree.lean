module

public import Init

@[expose] public section
set_option autoImplicit false
namespace DosenPetric
universe u

/-- Explicit finite rooted trees; node multiplicity and order are retained. -/
inductive TraceTree (α : Type u) where
  | node : α → List (TraceTree α) → TraceTree α

namespace TraceTree
variable {α : Type u}

def root : TraceTree α → α | .node a _ => a
def children : TraceTree α → List (TraceTree α) | .node _ ts => ts
def nodes : TraceTree α → List α | .node a ts => a :: ts.flatMap nodes
def count : TraceTree α → Nat | .node _ ts => 1 + (ts.map count).sum

theorem root_mem (t : TraceTree α) : t.root ∈ t.nodes := by cases t; simp [root,nodes]
theorem count_pos (t : TraceTree α) : 0 < t.count := by cases t; simp only [count]; omega

theorem node_mem (a b : α) (ts : List (TraceTree α)) :
    b ∈ (TraceTree.node a ts).nodes ↔ b = a ∨ ∃ t ∈ ts, b ∈ t.nodes := by
  simp only [nodes, List.mem_cons, List.mem_flatMap]

theorem count_nodes (t : TraceTree α) : t.count = t.nodes.length := by
  cases t with
  | node a ts =>
    simp only [count,nodes,List.length_cons,List.length_flatMap]
    have hh : ts.map count = ts.map (fun t => t.nodes.length) := by
      apply List.map_congr_left
      intro t ht
      exact count_nodes t
    rw [hh]
    omega
termination_by sizeOf t
decreasing_by
  have h := List.sizeOf_lt_of_mem ht
  simp only [TraceTree.node.sizeOf_spec]
  omega

end TraceTree

theorem nat_le_map_sum {α : Type u} (f : α → Nat) {xs : List α} {a : α}
    (ha : a ∈ xs) : f a ≤ (xs.map f).sum := by
  induction xs with
  | nil => cases ha
  | cons b xs ih =>
    simp only [List.map_cons, List.sum_cons]
    cases List.mem_cons.mp ha with
    | inl h => cases h; omega
    | inr h => have hh := ih h; omega

/-- A finite branching relation with an explicit decreasing level. -/
structure FiniteTrace (α : Type u) where
  edge : α → α → Prop
  next : α → List α
  next_correct : ∀ a b, b ∈ next a ↔ edge a b
  level : α → Nat
  decreases : ∀ {a b}, edge a b → level b < level a

namespace FiniteTrace
variable {α : Type u} (S : FiniteTrace α)

inductive Reach (R : α → α → Prop) : α → α → Prop where
  | root (a) : Reach R a a
  | step {a b c} : R a b → Reach R b c → Reach R a c

theorem Reach.trans {R : α → α → Prop} {a b c : α}
    (h : Reach R a b) (k : Reach R b c) : Reach R a c := by
  induction h with
  | root => exact k
  | step he _ ih => exact .step he (ih k)

def tree (S : FiniteTrace α) (a : α) : TraceTree α :=
  .node a ((S.next a).attach.map fun b => S.tree b.val)
termination_by S.level a
decreasing_by exact S.decreases ((S.next_correct _ _).mp b.property)

theorem tree_eq (a : α) :
    S.tree a = .node a ((S.next a).attach.map fun b => S.tree b.val) := by rw [tree]

theorem tree_root (a : α) : (S.tree a).root = a := by rw [tree_eq]; rfl

theorem tree_sound (S : FiniteTrace α) (a b : α)
    (h : b ∈ (S.tree a).nodes) : Reach S.edge a b := by
  rw [tree_eq,TraceTree.node_mem] at h
  rcases h with h | ⟨t,ht,hb⟩
  · cases h; exact .root a
  · obtain ⟨⟨c,hc⟩,_,rfl⟩ := List.mem_map.mp ht
    exact .step ((S.next_correct a c).mp hc) (S.tree_sound c b hb)
termination_by S.level a
decreasing_by exact S.decreases ((S.next_correct a c).mp hc)

theorem tree_complete {a b : α} (h : Reach S.edge a b) : b ∈ (S.tree a).nodes := by
  induction h with
  | root a =>
    have h := TraceTree.root_mem (S.tree a)
    rwa [S.tree_root a] at h
  | @step a c b he _ ih =>
    rw [tree_eq,TraceTree.node_mem]
    have hc := (S.next_correct a c).mpr he
    refine .inr ⟨S.tree c,?_,ih⟩
    exact List.mem_map.mpr ⟨⟨c,hc⟩,List.mem_attach _ _,rfl⟩

/-- The explicit finite node list is exactly finite predecessor reachability. -/
theorem tree_correct (a b : α) : b ∈ (S.tree a).nodes ↔ Reach S.edge a b :=
  ⟨S.tree_sound a b, S.tree_complete⟩

def rank (a : α) : Nat := (S.tree a).count

theorem map_attach_values (xs : List α) (f : α → Nat) :
    (xs.attach.map fun a => f a.val).sum = (xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons => simp

theorem rank_eq (a : α) : S.rank a = 1 + ((S.next a).map S.rank).sum := by
  rw [rank,tree_eq,TraceTree.count,List.map_map]
  exact congrArg (fun n => 1+n) (map_attach_values (S.next a) S.rank)

theorem rank_pos (a : α) : 0 < S.rank a := TraceTree.count_pos _

theorem child_rank_lt {a b : α} (h : S.edge a b) : S.rank b < S.rank a := by
  have hh := nat_le_map_sum S.rank ((S.next_correct a b).mpr h)
  rw [rank_eq S a]; omega

theorem rank_one_iff (a : α) : S.rank a = 1 ↔ S.next a = [] := by
  rw [rank_eq]
  cases h : S.next a with
  | nil => simp
  | cons b bs =>
    have hp := S.rank_pos b
    simp only [List.map_cons,List.sum_cons]
    constructor
    · intro hh; omega
    · intro hh; cases hh

end FiniteTrace
end DosenPetric
