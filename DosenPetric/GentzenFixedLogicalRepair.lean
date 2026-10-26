module

public import DosenPetric.GentzenFixedLogicalSquare
public import DosenPetric.GentzenCenteredBounds

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

def repairL (f : G P (Γ++A::B::Θ) Δ) : G P K Δ :=
  (q.normalizeContext g t [.conj A B] hq).inverse.left
    (G.conjL (C::g.erased) t.erased Δ A B
      ((p.normalizeContext g t [A,B] hp).left (p.performL Δ f)))

theorem repair_countL (f : G P (Γ++A::B::Θ) Δ) : (repairL g t q p hq hp f).cutCount=f.cutCount := by
  rw [repairL,ExchangeScript.left_count]
  change ((p.normalizeContext g t [A,B] hp).left (p.performL Δ f)).cutCount=f.cutCount
  rw [ExchangeScript.left_count,ContractionSelection.performL_count]

theorem denoteL (f : G P (Γ++A::B::Θ) Δ) :
    ofTerm (repairL g t q p hq hp f).denote=ofTerm (q.performL Δ (G.conjL Γ Θ Δ A B f)).denote := by
  rw [repairL,ExchangeScript.left_denote,ContractionSelection.performL_denote]
  change comp ((q.normalizeContext g t [.conj A B] hq).inverse.arrow .conj)
      (comp (ofTerm (Rules.conjLeft (C::g.erased) t.erased A B).toTerm)
        (ofTerm ((p.normalizeContext g t [A,B] hp).left (p.performL Δ f)).denote))=
    comp (ofTerm q.route.product) (comp (ofTerm (Rules.conjLeft Γ Θ A B).toTerm) (ofTerm f.denote))
  rw [ExchangeScript.left_denote,ContractionSelection.performL_denote,conjLeft_compare,conjLeft_compare]
  let d : (side P .conj).Hom (ante (Γ++A::B::Θ)) (succ Δ):=ofTerm f.denote
  change (side P .conj).comp ((q.normalizeContext g t [.conj A B] hq).inverse.arrow .conj)
      ((side P .conj).comp (logicalSide .conj (C::g.erased) t.erased A B)
        ((side P .conj).comp ((p.normalizeContext g t [A,B] hp).arrow .conj)
          ((side P .conj).comp (p.route.sideArrow .conj) d)))=
    (side P .conj).comp (q.route.sideArrow .conj) ((side P .conj).comp (logicalSide .conj Γ Θ A B) d)
  symm
  simpa only [(side P .conj).assoc] using
    congrArg (fun h=>(side P .conj).comp h d) (square g t .conj A B q p hq hp)

include hq hp in
theorem old_rankL (f : G P (Γ++A::B::Θ) Δ) (hn : 2≤q.arity) :
    (q.performL Δ (G.conjL Γ Θ Δ A B f)).rho .left q.keep=
      (p.selected.map (fun a=>f.rho .left a)).sum+q.arity+1 := by
  let O : At K C→Nat:=(q.performL Δ (G.conjL Γ Θ Δ A B f)).rho .left
  let r0 : At (Γ++A::B::Θ) C→Nat:=f.rho .left
  let r1 : At (Γ++.conj A B::Θ) C→Nat:=(G.conjL Γ Θ Δ A B f).rho .left
  have he:=context_sum_step g t A B (.conj A B) q p hq hp r0 r1
    (fun a=>G.rho_conjL_surviving Γ Θ Δ A B f _ _ (At.fixed_before ..))
    (fun a=>G.rho_conjL_surviving Γ Θ Δ A B f _ _ (At.fixed_tail ..))
  have hh:=q.performL_rank Δ (G.conjL Γ Θ Δ A B f)
  change O q.keep=(q.selected.map r1).sum+_ at hh
  rw [ite_eq_left hn,he] at hh
  exact hh
end Left

section Right
variable (q : ContractionSelection C (Γ++.disj A B::Θ) K)
variable (p : ContractionSelection C (Γ++A::B::Θ) L)
variable (hq : q.mask=SelectionMask.contextMask g t [.disj A B])
variable (hp : p.mask=SelectionMask.contextMask g t [A,B])

def repairR (f : G P Δ (Γ++A::B::Θ)) : G P Δ K :=
  (q.normalizeContext g t [.disj A B] hq).inverse.right
    (G.disjR Δ (C::g.erased) t.erased A B
      ((p.normalizeContext g t [A,B] hp).right (p.performR Δ f)))

theorem repair_countR (f : G P Δ (Γ++A::B::Θ)) : (repairR g t q p hq hp f).cutCount=f.cutCount := by
  rw [repairR,ExchangeScript.right_count]
  change ((p.normalizeContext g t [A,B] hp).right (p.performR Δ f)).cutCount=f.cutCount
  rw [ExchangeScript.right_count,ContractionSelection.performR_count]

theorem denoteR (f : G P Δ (Γ++A::B::Θ)) :
    ofTerm (repairR g t q p hq hp f).denote=ofTerm (q.performR Δ (G.disjR Δ Γ Θ A B f)).denote := by
  rw [repairR,ExchangeScript.right_denote,ContractionSelection.performR_denote]
  change comp (comp (ofTerm ((p.normalizeContext g t [A,B] hp).right (p.performR Δ f)).denote)
      (ofTerm (Rules.disjRight (C::g.erased) t.erased A B).toTerm))
      ((q.normalizeContext g t [.disj A B] hq).inverse.arrow .disj)=
    comp (comp (ofTerm f.denote) (ofTerm (Rules.disjRight Γ Θ A B).toTerm)) (ofTerm q.route.coproduct)
  rw [ExchangeScript.right_denote,ContractionSelection.performR_denote,disjRight_compare,disjRight_compare]
  let d : (side P .disj).Hom (succ (Γ++A::B::Θ)) (ante Δ):=ofTerm f.denote
  change (side P .disj).comp ((q.normalizeContext g t [.disj A B] hq).inverse.arrow .disj)
      ((side P .disj).comp (logicalSide .disj (C::g.erased) t.erased A B)
        ((side P .disj).comp ((p.normalizeContext g t [A,B] hp).arrow .disj)
          ((side P .disj).comp (p.route.sideArrow .disj) d)))=
    (side P .disj).comp (q.route.sideArrow .disj) ((side P .disj).comp (logicalSide .disj Γ Θ A B) d)
  symm
  simpa only [(side P .disj).assoc] using
    congrArg (fun h=>(side P .disj).comp h d) (square g t .disj A B q p hq hp)

include hq hp in
theorem old_rankR (f : G P Δ (Γ++A::B::Θ)) (hn : 2≤q.arity) :
    (q.performR Δ (G.disjR Δ Γ Θ A B f)).rho .right q.keep=
      (p.selected.map (fun a=>f.rho .right a)).sum+q.arity+1 := by
  let O : At K C→Nat:=(q.performR Δ (G.disjR Δ Γ Θ A B f)).rho .right
  let r0 : At (Γ++A::B::Θ) C→Nat:=f.rho .right
  let r1 : At (Γ++.disj A B::Θ) C→Nat:=(G.disjR Δ Γ Θ A B f).rho .right
  have he:=context_sum_step g t A B (.disj A B) q p hq hp r0 r1
    (fun a=>G.rho_disjR_surviving Δ Γ Θ A B f _ _ (At.fixed_before ..))
    (fun a=>G.rho_disjR_surviving Δ Γ Θ A B f _ _ (At.fixed_tail ..))
  have hh:=q.performR_rank Δ (G.disjR Δ Γ Θ A B f)
  change O q.keep=(q.selected.map r1).sum+_ at hh
  rw [ite_eq_left hn,he] at hh
  exact hh
end Right
end DosenPetric.Reduced.Gentzen.FixedLogicalReducer
