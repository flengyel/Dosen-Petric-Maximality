module

public import DosenPetric.GentzenOutsideTransport

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ProofSpine
variable {Γ Δ I J U V : List (NormalForm P)}
variable {root : G P Γ Δ} {g : G P I J} {v : G P U V}

/-- Incomparable paths supply the actual sibling divergence internally. -/
theorem apart_of_incomparable (a : ProofSpine root g) (b : ProofSpine root v)
    (hab : ¬ ∃ xs, a.path++xs=b.path) (hba : ¬ ∃ xs, b.path++xs=a.path) :
    SpineApart a b := by
  induction a with
  | root=>exact False.elim (hab ⟨b.path,rfl⟩)
  | @down Γ Δ I J U V root f g p a ih=>
    cases b with
    | root=>exact False.elim (hba ⟨(ProofSpine.down p a).path,rfl⟩)
    | @down _ _ I' J' U' V' _ k v q b=>
      by_cases hp : p.branch=q.branch
      · have he : (⟨I,J,f,p⟩ : Branch root)=⟨I',J',k,q⟩:=Branch.eq_of_branch _ _ hp
        cases he
        apply SpineApart.down p a b
        apply ih b
        · rintro ⟨xs,hx⟩
          apply hab
          exact ⟨xs,congrArg (List.cons p.branch) hx⟩
        · rintro ⟨xs,hx⟩
          apply hba
          exact ⟨xs,congrArg (List.cons p.branch) hx⟩
      · exact .fork p q a b hp
end ProofSpine
namespace ProofAddress
variable {Γ Δ I J U V : List (NormalForm P)}
variable {root : G P Γ Δ} {g : G P I J} {v : G P U V}

/-- Full outside-path transport, with no caller-supplied branch decomposition. -/
theorem outside_of_incomparable (a : ProofAddress root g) (b : ProofAddress root v)
    (hab : ¬ ∃ xs, a.path++xs=b.path) (hba : ¬ ∃ xs, b.path++xs=a.path)
    (h : G P I J) :
    ∃ c : ProofAddress (a.replace h) v,
      c.path=b.path ∧ ∀ (s : SequentSide) {C : NormalForm P} (x : Place s U V C),
        c.ascend s x=b.ascend s x := by
  apply a.outside_transport b _ h
  apply a.spine.apart_of_incomparable b.spine
  · simpa only [spine_path] using hab
  · simpa only [spine_path] using hba

/-- Cluster membership of every unchanged outside position is equivalent
before and after replacement; no occurrence-relation faithfulness is used. -/
theorem outside_cluster (a : ProofAddress root g) (b : ProofAddress root v)
    (hab : ¬ ∃ xs, a.path++xs=b.path) (hba : ¬ ∃ xs, b.path++xs=a.path)
    (h : G P I J) :
    ∃ c : ProofAddress (a.replace h) v, c.path=b.path ∧
      ∀ (s : SequentSide) {C : NormalForm P} (x : Place s Γ Δ C) (y : Place s U V C),
        (c.traceAt s y ∈ ((a.replace h).cluster s x).nodes ↔
          b.traceAt s y ∈ (root.cluster s x).nodes) := by
  obtain ⟨c,hc,he⟩:=a.outside_of_incomparable b hab hba h
  refine ⟨c,hc,?_⟩
  intro s C x y
  rw [c.cluster_iff_ascend,b.cluster_iff_ascend,he]
end ProofAddress
end DosenPetric.Reduced.Gentzen
