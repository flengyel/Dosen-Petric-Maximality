module

public import DosenPetric.GentzenSelectedSourceRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.SelectedLogicalReducer
universe u
variable {P : Type u} {A B : NormalForm P} {Γ Θ K L Δ : List (NormalForm P)}

section Left
variable (g : SelectionMask (.conj A B) Γ) (t : SelectionMask (.conj A B) Θ)
variable (q : ContractionSelection (.conj A B) (Γ++.conj A B::Θ) K)
variable (p : ContractionSelection (.conj A B) (Γ++Θ) L)
variable (hq : q.mask=SelectionMask.selectedContext g t) (hp : p.mask=g.append t)

include hq hp in
theorem old_rankL (f : G P (Γ++A::B::Θ) Δ) (hn : 2≤q.arity) :
    (q.performL Δ (G.conjL Γ Θ Δ A B f)).rho .left q.keep=
      (p.selected.map (fun a=>f.rho .left (At.reinsert Γ Θ [A,B] a))).sum+q.arity+1 := by
  let O : At K (.conj A B)→Nat:=(q.performL Δ (G.conjL Γ Θ Δ A B f)).rho .left
  let r0 : At (Γ++Θ) (.conj A B)→Nat:=fun a=>f.rho .left (At.reinsert Γ Θ [A,B] a)
  let r1 : At (Γ++.conj A B::Θ) (.conj A B)→Nat:=(G.conjL Γ Θ Δ A B f).rho .left
  have hfirst (a : At Γ (.conj A B)) : r1 (a.before (.conj A B::Θ))=1+r0 (a.before Θ) := by
    have h:=G.rho_conjL_surviving Γ Θ Δ A B f _ _ (At.fixed_before Γ [A,B] [.conj A B] Θ a)
    exact h.trans (congrArg (fun x : At (Γ++A::B::Θ) (.conj A B)=>1+f.rho .left x)
      (At.reinsert_before Γ Θ [A,B] a)).symm
  have hlast (a : At Θ (.conj A B)) : r1 (At.shift Γ a.there)=1+r0 (At.shift Γ a) := by
    have h:=G.rho_conjL_surviving Γ Θ Δ A B f _ _ (At.fixed_tail Γ [A,B] [.conj A B] Θ a)
    exact h.trans (congrArg (fun x : At (Γ++A::B::Θ) (.conj A B)=>1+f.rho .left x)
      (At.reinsert_shift Γ Θ [A,B] a)).symm
  have he:=selected_sum_step g t q p hq hp r0 r1 hfirst hlast (G.rho_conjL_principal Γ Θ Δ A B f)
  have hh:=q.performL_rank Δ (G.conjL Γ Θ Δ A B f)
  change O q.keep=(q.selected.map r1).sum+_ at hh
  rw [ite_eq_left hn,he] at hh
  exact hh

include hq hp in
theorem source_thresholdL (f : G P (Γ++A::B::Θ) Δ) (hn : 2≤q.arity) :
    sourceInnerL p (G.moveEndL Γ [A,B] Θ Δ f)+1≤
      (q.performL Δ (G.conjL Γ Θ Δ A B f)).rho .left q.keep := by
  let r0 : At (Γ++Θ) (.conj A B)→Nat:=fun a=>f.rho .left (At.reinsert Γ Θ [A,B] a)
  let O : At K (.conj A B)→Nat:=(q.performL Δ (G.conjL Γ Θ Δ A B f)).rho .left
  let N:=sourceInnerL p (G.moveEndL Γ [A,B] Θ Δ f)
  have h0:=old_rankL g t q p hq hp f hn
  have h1:=sourceInner_moveL p f
  have h2:=arity_balance g t q p hq hp
  change O q.keep=(p.selected.map r0).sum+q.arity+1 at h0
  change N=(p.selected.map r0).sum+p.arity+_ at h1
  change N+1≤O q.keep
  split at h1 <;> omega
end Left

section Right
variable (g : SelectionMask (.disj A B) Γ) (t : SelectionMask (.disj A B) Θ)
variable (q : ContractionSelection (.disj A B) (Γ++.disj A B::Θ) K)
variable (p : ContractionSelection (.disj A B) (Γ++Θ) L)
variable (hq : q.mask=SelectionMask.selectedContext g t) (hp : p.mask=g.append t)

include hq hp in
theorem old_rankR (f : G P Δ (Γ++A::B::Θ)) (hn : 2≤q.arity) :
    (q.performR Δ (G.disjR Δ Γ Θ A B f)).rho .right q.keep=
      (p.selected.map (fun a=>f.rho .right (At.reinsert Γ Θ [A,B] a))).sum+q.arity+1 := by
  let O : At K (.disj A B)→Nat:=(q.performR Δ (G.disjR Δ Γ Θ A B f)).rho .right
  let r0 : At (Γ++Θ) (.disj A B)→Nat:=fun a=>f.rho .right (At.reinsert Γ Θ [A,B] a)
  let r1 : At (Γ++.disj A B::Θ) (.disj A B)→Nat:=(G.disjR Δ Γ Θ A B f).rho .right
  have hfirst (a : At Γ (.disj A B)) : r1 (a.before (.disj A B::Θ))=1+r0 (a.before Θ) := by
    have h:=G.rho_disjR_surviving Δ Γ Θ A B f _ _ (At.fixed_before Γ [A,B] [.disj A B] Θ a)
    exact h.trans (congrArg (fun x : At (Γ++A::B::Θ) (.disj A B)=>1+f.rho .right x)
      (At.reinsert_before Γ Θ [A,B] a)).symm
  have hlast (a : At Θ (.disj A B)) : r1 (At.shift Γ a.there)=1+r0 (At.shift Γ a) := by
    have h:=G.rho_disjR_surviving Δ Γ Θ A B f _ _ (At.fixed_tail Γ [A,B] [.disj A B] Θ a)
    exact h.trans (congrArg (fun x : At (Γ++A::B::Θ) (.disj A B)=>1+f.rho .right x)
      (At.reinsert_shift Γ Θ [A,B] a)).symm
  have he:=selected_sum_step g t q p hq hp r0 r1 hfirst hlast (G.rho_disjR_principal Δ Γ Θ A B f)
  have hh:=q.performR_rank Δ (G.disjR Δ Γ Θ A B f)
  change O q.keep=(q.selected.map r1).sum+_ at hh
  rw [ite_eq_left hn,he] at hh
  exact hh

include hq hp in
theorem source_thresholdR (f : G P Δ (Γ++A::B::Θ)) (hn : 2≤q.arity) :
    sourceInnerR p (G.moveEndR Δ Γ [A,B] Θ f)+1≤
      (q.performR Δ (G.disjR Δ Γ Θ A B f)).rho .right q.keep := by
  let r0 : At (Γ++Θ) (.disj A B)→Nat:=fun a=>f.rho .right (At.reinsert Γ Θ [A,B] a)
  let O : At K (.disj A B)→Nat:=(q.performR Δ (G.disjR Δ Γ Θ A B f)).rho .right
  let N:=sourceInnerR p (G.moveEndR Δ Γ [A,B] Θ f)
  have h0:=old_rankR g t q p hq hp f hn
  have h1:=sourceInner_moveR p f
  have h2:=arity_balance g t q p hq hp
  change O q.keep=(p.selected.map r0).sum+q.arity+1 at h0
  change N=(p.selected.map r0).sum+p.arity+_ at h1
  change N+1≤O q.keep
  split at h1 <;> omega
end Right
end DosenPetric.Reduced.Gentzen.SelectedLogicalReducer
