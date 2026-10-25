module

public import DosenPetric.GentzenAddressPaths

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace TraceNode
variable {s : SequentSide} {C : NormalForm P}

theorem reach_ascend {Γ Δ : List (NormalForm P)} {root : G P Γ Δ}
    {n m : TraceNode P s C} (h : FiniteTrace.Reach Edge n m)
    (a : ProofAddress root n.proof) (ha : a.path = n.address)
    (x : Place s Γ Δ C) (hx : a.ascend s n.position = some x) :
    ∃ b : ProofAddress root m.proof, b.path = m.address ∧ b.ascend s m.position = some x := by
  induction h with
  | root => exact ⟨a,ha,hx⟩
  | step he _ ih =>
    obtain ⟨q,hq,rfl⟩ := he
    apply ih (a.down q.branch.occurrence)
    · exact congrArg (fun p => p ++ [q.branch.occurrence.branch]) ha
    · change (q.branch.occurrence.parent s q.position).bind (a.ascend s) = some x
      rw [hq]
      exact hx

end TraceNode

namespace ProofAddress
variable {Γ Δ Θ Λ Ξ Ω : List (NormalForm P)}
variable {root : G P Γ Δ} {g : G P Θ Λ} {v : G P Ξ Ω}

theorem cluster_ascend (a : ProofAddress root g) (s : SequentSide) {C : NormalForm P}
    (x : Place s Γ Δ C) (y : Place s Θ Λ C)
    (hm : a.traceAt s y ∈ (root.cluster s x).nodes) : a.ascend s y = some x := by
  have hh := (root.cluster_correct s x (a.traceAt s y)).mp hm
  obtain ⟨b,hb,hx⟩ := TraceNode.reach_ascend hh ProofAddress.root rfl x rfl
  have he : b = a := eq_of_path b a hb
  cases he
  exact hx

theorem cluster_iff_ascend (a : ProofAddress root g) (s : SequentSide) {C : NormalForm P}
    (x : Place s Γ Δ C) (y : Place s Θ Λ C) :
    a.traceAt s y ∈ (root.cluster s x).nodes ↔ a.ascend s y = some x :=
  ⟨a.cluster_ascend s x y,fun hh => (root.cluster_correct s x _).mpr (a.ascend_reach s x y hh)⟩

theorem ascend_replacement (a : ProofAddress root g) (h : G P Θ Λ)
    (b : ProofAddress h v) (s : SequentSide) {C : NormalForm P} (y : Place s Ξ Ω C) :
    ((a.inserted h).append b).ascend s y = (b.ascend s y).bind (a.ascend s) := by
  rw [ascend_append]
  cases hb : b.ascend s y with
  | none => rfl
  | some z => exact a.ascend_inserted h s z

theorem replacement_cluster_iff (a : ProofAddress root g) (h : G P Θ Λ)
    (b : ProofAddress h v) (s : SequentSide) {C : NormalForm P}
    (x : Place s Γ Δ C) (y : Place s Ξ Ω C) :
    ((a.inserted h).append b).traceAt s y ∈ ((a.replace h).cluster s x).nodes ↔
      ∃ z : Place s Θ Λ C, b.ascend s y = some z ∧ a.ascend s z = some x := by
  rw [cluster_iff_ascend,ascend_replacement]
  cases hb : b.ascend s y with
  | none => simp
  | some z => simp

theorem cluster_rank_lt (a : ProofAddress root g) (s : SequentSide) {C : NormalForm P}
    (x : Place s Γ Δ C) (y : Place s Θ Λ C)
    (hm : a.traceAt s y ∈ (root.cluster s x).nodes) (hp : a.path ≠ []) :
    g.rho s y < root.rho s x :=
  a.ascend_rank_lt s x y (a.cluster_ascend s x y hm) hp

end ProofAddress
end DosenPetric.Reduced.Gentzen
