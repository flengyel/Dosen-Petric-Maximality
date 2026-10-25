module

public import DosenPetric.GentzenReducibleOccurrences

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace TraceNode
variable {s : SequentSide} {C : NormalForm P}

theorem rank_eq_rho (n : TraceNode P s C) : n.rank = n.proof.rho s n.position :=
  rank_readdress n.proof s n.position n.address []

theorem edge_rank_lt {n m : TraceNode P s C} (h : Edge n m) : m.rank < n.rank :=
  (system P s C).child_rank_lt h

theorem reach_rank_le {n m : TraceNode P s C} (h : FiniteTrace.Reach Edge n m) :
    m.rank ≤ n.rank := by
  induction h with
  | root => exact Nat.le_refl _
  | step he _ ih => exact Nat.le_trans ih (Nat.le_of_lt (edge_rank_lt he))

theorem reach_rank_lt {n m : TraceNode P s C} (h : FiniteTrace.Reach Edge n m)
    (hn : n.address ≠ m.address) : m.rank < n.rank := by
  cases h with
  | root => exact False.elim (hn rfl)
  | step he ht => exact Nat.lt_of_le_of_lt (reach_rank_le ht) (edge_rank_lt he)

end TraceNode

namespace Premise
variable {Γ Δ Θ Λ : List (NormalForm P)} {f : G P Γ Δ} {g : G P Θ Λ}

theorem inserted_parent (p : Premise f g) (h : G P Θ Λ) (s : SequentSide)
    {C : NormalForm P} (y : Place s Θ Λ C) :
    (p.inserted h).parent s y = p.parent s y := by cases p <;> cases s <;> rfl

end Premise

namespace ProofAddress
variable {Γ Δ Θ Λ Ξ Ω : List (NormalForm P)}
variable {root : G P Γ Δ} {g : G P Θ Λ} {h : G P Ξ Ω}

/-- Follow an actual whole-formula position upward through this proof address. -/
def ascend : {Θ Λ : List (NormalForm P)} → {g : G P Θ Λ} →
    ProofAddress root g → (s : SequentSide) → {C : NormalForm P} →
    Place s Θ Λ C → Option (Place s Γ Δ C)
  | _,_,_,.root,_,_,y => some y
  | _,_,_,.down a p,s,_,y => (p.parent s y).bind (a.ascend s)

theorem ascend_root (s : SequentSide) {C : NormalForm P} (x : Place s Γ Δ C) :
    (.root : ProofAddress root root).ascend s x = some x := rfl

theorem ascend_down (a : ProofAddress root g) (p : Premise g h) (s : SequentSide)
    {C : NormalForm P} (y : Place s Ξ Ω C) :
    (a.down p).ascend s y = (p.parent s y).bind (a.ascend s) := rfl

theorem ascend_append (a : ProofAddress root g) (b : ProofAddress g h) (s : SequentSide)
    {C : NormalForm P} (y : Place s Ξ Ω C) :
    (a.append b).ascend s y = (b.ascend s y).bind (a.ascend s) := by
  induction b with
  | root => rfl
  | down b p ih =>
    simp only [append,ascend]
    cases hp : p.parent s y with
    | none => rfl
    | some z => exact ih z

theorem ascend_inserted (a : ProofAddress root g) (k : G P Θ Λ) (s : SequentSide)
    {C : NormalForm P} (y : Place s Θ Λ C) :
    (a.inserted k).ascend s y = a.ascend s y := by
  induction a with
  | root => rfl
  | down a p ih =>
    simp only [inserted,ascend,Premise.inserted_parent]
    cases hp : p.parent s y with
    | none => rfl
    | some z => exact ih (p.rebuild k) z

theorem trace_edge (a : ProofAddress root g) (p : Premise g h) (s : SequentSide)
    {C : NormalForm P} (x : Place s Θ Λ C) (y : Place s Ξ Ω C)
    (hp : p.parent s y = some x) :
    TraceNode.Edge (a.traceAt s x) ((a.down p).traceAt s y) :=
  ⟨⟨⟨_,_,h,p⟩,y⟩,hp,rfl⟩

theorem ascend_reach (a : ProofAddress root g) (s : SequentSide) {C : NormalForm P}
    (x : Place s Γ Δ C) (y : Place s Θ Λ C) (ha : a.ascend s y = some x) :
    FiniteTrace.Reach TraceNode.Edge (root.traceRoot s x) (a.traceAt s y) := by
  induction a with
  | root =>
    have he := Option.some.inj ha
    cases he
    exact .root _
  | down a p ih =>
    change (p.parent s y).bind (a.ascend s) = some x at ha
    cases hp : p.parent s y with
    | none => simp only [hp,Option.bind_none] at ha; cases ha
    | some z =>
      have hz : a.ascend s z = some x := by simpa only [hp,Option.bind_some] using ha
      exact (ih z hz).trans (.step (a.trace_edge p s z y hp) (.root _))

theorem ascend_rank_le (a : ProofAddress root g) (s : SequentSide) {C : NormalForm P}
    (x : Place s Γ Δ C) (y : Place s Θ Λ C) (ha : a.ascend s y = some x) :
    g.rho s y ≤ root.rho s x := by
  have hh := TraceNode.reach_rank_le (a.ascend_reach s x y ha)
  simpa only [TraceNode.rank_eq_rho,traceAt,G.traceRoot] using hh

theorem ascend_rank_lt (a : ProofAddress root g) (s : SequentSide) {C : NormalForm P}
    (x : Place s Γ Δ C) (y : Place s Θ Λ C) (ha : a.ascend s y = some x)
    (hp : a.path ≠ []) : g.rho s y < root.rho s x := by
  have hh := TraceNode.reach_rank_lt (a.ascend_reach s x y ha) (Ne.symm hp)
  simpa only [TraceNode.rank_eq_rho,traceAt,G.traceRoot] using hh

end ProofAddress
end DosenPetric.Reduced.Gentzen
