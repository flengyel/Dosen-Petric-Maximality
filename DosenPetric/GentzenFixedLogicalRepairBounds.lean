module

public import DosenPetric.GentzenFixedLogicalRepair

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.FixedLogicalReducer
universe u
variable {P : Type u} {C A B : NormalForm P} {Γ Θ K L Δ : List (NormalForm P)}
variable (g : SelectionMask C Γ) (t : SelectionMask C Θ)

section Left
variable (q : ContractionSelection C (Γ++.conj A B::Θ) K)
variable (p : ContractionSelection C (Γ++A::B::Θ) L)
variable (hq : q.mask=SelectionMask.contextMask g t [.conj A B])
variable (hp : p.mask=SelectionMask.contextMask g t [A,B])

theorem repair_boundL (f : G P (Γ++A::B::Θ) Δ) (hn : 2≤q.arity) :
    ContractionBound .left C ((q.performL Δ (G.conjL Γ Θ Δ A B f)).rho .left q.keep)
      (repairL g t q p hq hp f) (fun a=>a=q.keep) := by
  have hb : (p.performL Δ f).rho .left p.keep<
      (q.performL Δ (G.conjL Γ Θ Δ A B f)).rho .left q.keep := by
    let R : At L C→Nat:=(p.performL Δ f).rho .left
    let O : At K C→Nat:=(q.performL Δ (G.conjL Γ Θ Δ A B f)).rho .left
    let rf : At (Γ++A::B::Θ) C→Nat:=f.rho .left
    have h0:=old_rankL g t q p hq hp f hn
    have h1:=p.performL_rank Δ f
    change O q.keep=(p.selected.map rf).sum+q.arity+1 at h0
    change R p.keep=(p.selected.map rf).sum+_ at h1
    change R p.keep<O q.keep
    split at h1 <;> omega
  have hi:=(p.normalizeContext g t [A,B] hp).bound_at_left p.keep
    (p.normalizeContext_keep g t [A,B] hp) (p.performL Δ f) hb
  have hm:=ContractionBound.conjL_head g.erased t.erased Δ A B _ hi
  exact (q.normalizeContext g t [.conj A B] hq).inverse_bound_left q.keep
    (q.normalizeContext_keep g t [.conj A B] hq) _ hm
end Left

section Right
variable (q : ContractionSelection C (Γ++.disj A B::Θ) K)
variable (p : ContractionSelection C (Γ++A::B::Θ) L)
variable (hq : q.mask=SelectionMask.contextMask g t [.disj A B])
variable (hp : p.mask=SelectionMask.contextMask g t [A,B])

theorem repair_boundR (f : G P Δ (Γ++A::B::Θ)) (hn : 2≤q.arity) :
    ContractionBound .right C ((q.performR Δ (G.disjR Δ Γ Θ A B f)).rho .right q.keep)
      (repairR g t q p hq hp f) (fun a=>a=q.keep) := by
  have hb : (p.performR Δ f).rho .right p.keep<
      (q.performR Δ (G.disjR Δ Γ Θ A B f)).rho .right q.keep := by
    let R : At L C→Nat:=(p.performR Δ f).rho .right
    let O : At K C→Nat:=(q.performR Δ (G.disjR Δ Γ Θ A B f)).rho .right
    let rf : At (Γ++A::B::Θ) C→Nat:=f.rho .right
    have h0:=old_rankR g t q p hq hp f hn
    have h1:=p.performR_rank Δ f
    change O q.keep=(p.selected.map rf).sum+q.arity+1 at h0
    change R p.keep=(p.selected.map rf).sum+_ at h1
    change R p.keep<O q.keep
    split at h1 <;> omega
  have hi:=(p.normalizeContext g t [A,B] hp).bound_at_right p.keep
    (p.normalizeContext_keep g t [A,B] hp) (p.performR Δ f) hb
  have hm:=ContractionBound.disjR_head Δ g.erased t.erased A B _ hi
  exact (q.normalizeContext g t [.disj A B] hq).inverse_bound_right q.keep
    (q.normalizeContext_keep g t [.disj A B] hq) _ hm
end Right
end DosenPetric.Reduced.Gentzen.FixedLogicalReducer
