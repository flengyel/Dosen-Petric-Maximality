module

public import DosenPetric.GentzenNonemptyLeftLogical

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionBound
variable {C : NormalForm P} {k : Nat}

theorem conjL (Γ Θ Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P (Γ++A::B::Θ) Δ) (E : At (Γ++.conj A B::Θ) C→Prop)
    (h : ContractionBound .left C k f
      (fun y=>∃ x,E x ∧ At.fixed Γ [A,B] [.conj A B] Θ y=some x)) :
    ContractionBound .left C k (G.conjL Γ Θ Δ A B f) E := by
  apply unary (Premise.conjL Γ Θ Δ A B f)
  · intro j;simpa only [G.branches,List.mem_singleton] using G.branches_complete j
  · intro x _ hx
    have ha:=(G.lowerContraction_iff_arity _ .left x).mp hx
    simp only [G.sourceArity] at ha
    split at ha <;> omega
  · exact h
end ContractionBound

namespace W4.NonemptyLeft
variable (d : Gentzen.SelectedLogical.Data P .conj) (hn : 1≤d.gs.length)
variable (Δ : List (NormalForm P)) (f : G P d.F Δ)

def innerRank : Nat := (inner d hn Δ f).rho .left d.inner.keep

theorem inner_bound : ContractionBound .left d.C (innerRank d hn Δ f+1) (inner d hn Δ f)
    (fun a=>a.index=d.inner.keep.index) := by
  apply ContractionBound.bounded
  intro a ha
  have he : a=d.inner.keep:=At.index_injective _ _ ha
  cases he
  exact Nat.lt_succ_self _

theorem middle_bound : ContractionBound .left d.C (innerRank d hn Δ f+1) (middle d hn Δ f)
    (fun a=>a.index=d.inner.keep.index ∨ a.index=d.s.I.length) := by
  apply ContractionBound.conjL d.s.I [] Δ d.A d.B
  apply (inner_bound d hn Δ f).mono
  rintro a ⟨x,hx,hp⟩
  change At d.I d.C at a
  change At d.J d.C at x
  change a.index=d.inner.keep.index
  change x.index=d.inner.keep.index ∨ x.index=d.s.I.length at hx
  have hi:=At.fixed_index d.s.I [d.A,d.B] [d.C] [] a
  rw [hp] at hi
  simp only [Option.map_some,List.length_cons,List.length_nil] at hi
  have ha : a.index<d.s.I.length+2 := by
    have h:=a.index_lt
    change a.index<(d.s.I++[d.A,d.B]).length at h
    rw [List.length_append] at h
    exact h
  unfold GapLogical.parentIndex at hi
  split at hi
  · have hh:=Option.some.inj hi
    omega
  · cases hi

theorem repair_bound : ContractionBound .left d.C (innerRank d hn Δ f+1) (repair d hn Δ f)
    (fun a=>a.index=d.x.index) := by
  apply d.last.left_bound (Nat.le_refl 2) Δ (middle d hn Δ f)
    (fun i=>i=d.x.index) (repair_blocked d hn Δ f)
  apply (middle_bound d hn Δ f).mono
  intro a ha
  change At d.J d.C at a
  have he : d.last.route.get a=d.last.keep := by
    apply At.index_injective
    exact (d.last.get_index a).trans (ha.trans (congrArg At.index d.last_keep).symm)
  have hm:=(d.last.selected_iff a).mpr he
  rw [d.last_selected,List.mem_cons,List.mem_singleton] at hm
  cases hm with
  | inl h=>
    cases h
    left
    change (d.s.inner.keep.before [d.C]).index=(d.s.inner.extend [d.A,d.B]).keep.index
    rw [ContractionBlock.extend_keep]
    exact (At.index_before d.s.inner.keep [d.C]).trans
      (At.index_before d.s.inner.keep [d.A,d.B]).symm
  | inr h=>
    cases h
    right
    change (At.shift d.s.I (.here d.C [])).index=d.s.I.length
    rw [At.index_shift,At.index,Nat.add_zero]
end W4.NonemptyLeft
end DosenPetric.Reduced.Gentzen
