module

public import DosenPetric.GentzenReducibility

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.Premise
universe u
variable {P : Type u} {Γ Δ Θ Λ I J : List (NormalForm P)}
variable {root : G P Γ Δ} {g : G P Θ Λ} {v : G P I J}

/-- A different immediate branch retains its proof, branch tag and parent map. -/
theorem sibling_exists (p : Premise root g) (q : Premise root v)
    (hn : p.branch≠q.branch) (h : G P Θ Λ) :
    ∃ r : Premise (p.rebuild h) v, r.branch=q.branch ∧
      ∀ (s : SequentSide) {C : NormalForm P} (x : Place s I J C),
        r.parent s x=q.parent s x := by
  have hq:=G.branches_complete (⟨I,J,v,q⟩ : Branch root)
  cases p <;> simp only [G.branches,List.mem_cons,List.not_mem_nil,or_false] at hq
  all_goals first
    | (cases hq; exact False.elim (hn rfl))
    | (rcases hq with hq | hq <;> cases hq)
  all_goals first
    | exact False.elim (hn rfl)
    | exact ⟨.conjR_left _ _,rfl,fun s _ _=>by cases s <;> rfl⟩
    | exact ⟨.conjR_right _ _,rfl,fun s _ _=>by cases s <;> rfl⟩
    | exact ⟨.disjL_left _ _,rfl,fun s _ _=>by cases s <;> rfl⟩
    | exact ⟨.disjL_right _ _,rfl,fun s _ _=>by cases s <;> rfl⟩
    | exact ⟨.mix_left _ _,rfl,fun s _ _=>by cases s <;> rfl⟩
    | exact ⟨.mix_right _ _,rfl,fun s _ _=>by cases s <;> rfl⟩
    | exact ⟨.cut_left _ _,rfl,fun s _ _=>by cases s <;> rfl⟩
    | exact ⟨.cut_right _ _,rfl,fun s _ _=>by cases s <;> rfl⟩

noncomputable def sibling (p : Premise root g) (q : Premise root v)
    (hn : p.branch≠q.branch) (h : G P Θ Λ) : Premise (p.rebuild h) v :=
  (p.sibling_exists q hn h).choose

theorem sibling_branch (p : Premise root g) (q : Premise root v)
    (hn : p.branch≠q.branch) (h : G P Θ Λ) : (p.sibling q hn h).branch=q.branch :=
  (p.sibling_exists q hn h).choose_spec.1

theorem sibling_parent (p : Premise root g) (q : Premise root v)
    (hn : p.branch≠q.branch) (h : G P Θ Λ) (s : SequentSide)
    {C : NormalForm P} (x : Place s I J C) :
    (p.sibling q hn h).parent s x=q.parent s x :=
  (p.sibling_exists q hn h).choose_spec.2 s x
end DosenPetric.Reduced.Gentzen.Premise
