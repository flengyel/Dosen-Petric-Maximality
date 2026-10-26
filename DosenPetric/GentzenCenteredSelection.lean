module

public import DosenPetric.GentzenMaskSelections
public import DosenPetric.GentzenExchangeScripts

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ExchangeScript
variable {F U : List (NormalForm P)}

def consFixed (A : NormalForm P) : {F U : List (NormalForm P)}→
    ExchangeScript P F U→ExchangeScript P (A::F) (A::U)
  | _,_,.identity F=>.identity (A::F)
  | _,_,.seq p q=>.seq (p.consFixed A) (q.consFixed A)
  | _,_,.exchange Γ X Y Θ=>.exchange (A::Γ) X Y Θ
  | _,_,.reindex hF hU p=>.reindex (congrArg (List.cons A) hF) (congrArg (List.cons A) hU) (p.consFixed A)

theorem consFixed_here (A : NormalForm P) (p : ExchangeScript P F U) :
    (p.consFixed A).get (.here A U)=.here A F := by
  induction p with
  | identity=>rfl
  | seq p q ih ih'=>exact (congrArg (p.consFixed A).get ih').trans ih
  | exchange Γ X Y Θ=>
    apply At.index_injective
    change (At.swapBlocks (A::Γ) X Y Θ (.here A _)).index=0
    rw [swapBlocks_index]
    simp only [At.index,List.length_cons,exchangeIndex]
    exact ite_eq_left (by omega)
  | reindex hF hU p ih=>cases hF;cases hU;exact ih

theorem consFixed_there (A : NormalForm P) (p : ExchangeScript P F U)
    {B : NormalForm P} (a : At U B) :
    (p.consFixed A).get a.there=(p.get a).there := by
  induction p with
  | identity=>rfl
  | seq p q ih ih'=>exact (congrArg (p.consFixed A).get (ih' a)).trans (ih (q.get a))
  | exchange Γ X Y Θ=>
    apply At.index_injective
    change (At.swapBlocks (A::Γ) X Y Θ a.there).index=(At.swapBlocks Γ X Y Θ a).there.index
    change (At.swapBlocks (A::Γ) X Y Θ a.there).index=(At.swapBlocks Γ X Y Θ a).index+1
    rw [swapBlocks_index,swapBlocks_index]
    simp only [List.length_cons,At.index,Nat.add_comm]
    unfold exchangeIndex
    split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega
  | reindex hF hU p ih=>cases hF;cases hU;exact ih a

def inverse : {F U : List (NormalForm P)}→ExchangeScript P F U→ExchangeScript P U F
  | _,_,.identity F=>.identity F
  | _,_,.seq p q=>.seq q.inverse p.inverse
  | _,_,.exchange Γ X Y Θ=>.exchange Γ Y X Θ
  | _,_,.reindex hF hU p=>.reindex hU hF p.inverse

theorem get_inverse (p : ExchangeScript P F U) {A : NormalForm P} (a : At F A) :
    p.get (p.inverse.get a)=a := by
  induction p with
  | identity=>rfl
  | seq p q ih ih'=>exact (congrArg p.get (ih' (p.inverse.get a))).trans (ih a)
  | exchange Γ X Y Θ=>exact At.swapBlocks_inverse Γ Y X Θ a
  | reindex hF hU p ih=>cases hF;cases hU;exact ih a

theorem inverse_get (p : ExchangeScript P F U) {A : NormalForm P} (a : At U A) :
    p.inverse.get (p.get a)=a := by
  apply p.injective
  exact p.get_inverse (p.get a)
end ExchangeScript

namespace ContractionSelection
variable {C : NormalForm P} {F K : List (NormalForm P)}

/-- Move the single retained copy to a distinguished head slot. This is a
finite script of existing exchanges, not a new proof constructor. -/
def center : {F K : List (NormalForm P)}→(p : ContractionSelection C F K)→
    ExchangeScript P (C::p.erased) K
  | _,_,.last Θ=>.identity (C::Θ)
  | _,_,.more p=>p.center
  | _,_,.fixed A p=>.seq (.exchange [] [A] [C] p.erased) (p.center.consFixed A)

theorem center_keep (p : ContractionSelection C F K) :
    p.center.get p.keep=.here C p.erased := by
  induction p with
  | last=>rfl
  | more p ih=>exact ih
  | fixed A p ih=>
    change At.swapBlocks [] [A] [C] p.erased ((p.center.consFixed A).get p.keep.there)=_
    rw [ExchangeScript.consFixed_there,ih]
    rfl

theorem center_erased (p : ContractionSelection C F K) {A : NormalForm P} (a : At p.erased A) :
    p.center.get (p.erasedRoute.get a)=a.there := by
  induction p with
  | last Θ=>simp only [erasedRoute,Route.get_map,Route.get_identity];rfl
  | more p ih=>exact ih a
  | fixed B p ih=>
    cases a with
    | here=>
      change At.swapBlocks [] [A] [C] p.erased ((p.center.consFixed A).get (.here A _))=_
      rw [ExchangeScript.consFixed_here]
      rfl
    | there a=>
      simp only [erasedRoute,Route.get,Route.get_map]
      change At.swapBlocks [] [B] [C] p.erased ((p.center.consFixed B).get (p.erasedRoute.get a).there)=_
      rw [ExchangeScript.consFixed_there,ih]
      rfl
end ContractionSelection
end DosenPetric.Reduced.Gentzen
