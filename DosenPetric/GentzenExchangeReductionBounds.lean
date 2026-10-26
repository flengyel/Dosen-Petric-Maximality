module

public import DosenPetric.GentzenExchangeFactorLaws

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.UnrestrictedExchange
universe u
variable {P : Type u} {C : NormalForm P} {Γ X Y Θ K K0 : List (NormalForm P)}
variable (q : ContractionSelection C (Γ++Y++X++Θ) K)
variable (p : ContractionSelection C (Γ++X++Y++Θ) K0) (r : ExchangeScript P K K0)
variable (hn : 2≤q.arity) (he : p.arity=q.arity) (hk : r.get p.keep=q.keep)
variable (hs : ∀ {A : NormalForm P} (a : At (Γ++X++Y++Θ) A),
  q.route.get (a.swapBlocks Γ X Y Θ)=r.get (p.route.get a))

include hs in
theorem denoteL {Δ : List (NormalForm P)} (t : G P (Γ++X++Y++Θ) Δ) :
    ofTerm (r.left (p.performL Δ t)).denote=
      ofTerm (q.performL Δ (G.exchangeL Γ X Y Θ Δ t)).denote := by
  rw [r.left_denote,p.performL_denote,q.performL_denote]
  let a : Hom (ante K) (ante K0):=r.arrow .conj
  let b : Hom (ante (Γ++Y++X++Θ)) (ante (Γ++X++Y++Θ)):=exchangeBack .conj Γ X Y Θ
  change comp a (comp (ofTerm p.route.product) (ofTerm t.denote))=
    comp (ofTerm q.route.product) (comp b (ofTerm t.denote))
  have h:=square q p r hs .conj
  change comp (ofTerm q.route.product) b=comp a (ofTerm p.route.product) at h
  rw [←Laws.assoc,←h,Laws.assoc]

include hs in
theorem denoteR {Δ : List (NormalForm P)} (t : G P Δ (Γ++X++Y++Θ)) :
    ofTerm (r.right (p.performR Δ t)).denote=
      ofTerm (q.performR Δ (G.exchangeR Δ Γ X Y Θ t)).denote := by
  rw [r.right_denote,p.performR_denote,q.performR_denote]
  let a : Hom (succ K0) (succ K):=r.arrow .disj
  let b : Hom (succ (Γ++X++Y++Θ)) (succ (Γ++Y++X++Θ)):=exchangeBack .disj Γ X Y Θ
  change comp (comp (ofTerm t.denote) (ofTerm p.route.coproduct)) a=
    comp (comp (ofTerm t.denote) b) (ofTerm q.route.coproduct)
  have h:=square q p r hs .disj
  change comp b (ofTerm q.route.coproduct)=comp (ofTerm p.route.coproduct) a at h
  rw [Laws.assoc,←h,←Laws.assoc]

include hn he hk hs in
theorem boundL {Δ : List (NormalForm P)} (t : G P (Γ++X++Y++Θ) Δ) :
    ContractionBound .left C
      ((q.performL Δ (G.exchangeL Γ X Y Θ Δ t)).rho .left q.keep)
      (r.left (p.performL Δ t)) (fun a=>a=q.keep) := by
  apply r.bound_left
  apply ContractionBound.bounded
  intro a ha
  have ha' : a=p.keep:=r.injective a p.keep (ha.trans hk.symm)
  cases ha'
  have h0:=old_rankL q p r hk hs t hn
  have h1:=p.performL_rank Δ t
  rw [ite_eq_left (by omega : 2≤p.arity)] at h1
  omega

include hn he hk hs in
theorem boundR {Δ : List (NormalForm P)} (t : G P Δ (Γ++X++Y++Θ)) :
    ContractionBound .right C
      ((q.performR Δ (G.exchangeR Δ Γ X Y Θ t)).rho .right q.keep)
      (r.right (p.performR Δ t)) (fun a=>a=q.keep) := by
  apply r.bound_right
  apply ContractionBound.bounded
  intro a ha
  have ha' : a=p.keep:=r.injective a p.keep (ha.trans hk.symm)
  cases ha'
  have h0:=old_rankR q p r hk hs t hn
  have h1:=p.performR_rank Δ t
  rw [ite_eq_left (by omega : 2≤p.arity)] at h1
  omega
end DosenPetric.Reduced.Gentzen.UnrestrictedExchange
