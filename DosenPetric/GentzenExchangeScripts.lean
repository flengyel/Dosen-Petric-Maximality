module

public import DosenPetric.GentzenRewiring
public import DosenPetric.GentzenLeftContractionBounds
public import DosenPetric.GentzenExchangeEmbeddings

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Derived scripts containing only existing exchange rules and equality
transports. These scripts introduce neither Gentzen rules nor contractions. -/
inductive ExchangeScript (P : Type u) : List (NormalForm P)→List (NormalForm P)→Type u where
  | identity (F) : ExchangeScript P F F
  | seq {F U K} : ExchangeScript P F U→ExchangeScript P U K→ExchangeScript P F K
  | exchange (Γ X Y Θ) : ExchangeScript P (Γ++Y++X++Θ) (Γ++X++Y++Θ)
  | reindex {F U K L} : F=K→U=L→ExchangeScript P F U→ExchangeScript P K L

namespace ExchangeScript
variable {F U K L Δ Γ : List (NormalForm P)}

def rewire : {F U : List (NormalForm P)}→ExchangeScript P F U→Rewire P F U
  | _,_,.identity F=>.identity F
  | _,_,.seq p q=>.seq p.rewire q.rewire
  | _,_,.exchange Γ X Y Θ=>.exchange Γ X Y Θ
  | _,_,.reindex hF hU p=>.reindex hF hU p.rewire

def get (p : ExchangeScript P F U) {A : NormalForm P} (a : At U A) : At F A := p.rewire.get a
def arrow (p : ExchangeScript P F U) (o : Op) := p.rewire.arrow o
def left (p : ExchangeScript P F U) (f : G P U Δ) : G P F Δ := p.rewire.left f
def right (p : ExchangeScript P F U) (f : G P Γ U) : G P Γ F := p.rewire.right f

theorem injective (p : ExchangeScript P F U) {A : NormalForm P} (a b : At U A)
    (h : p.get a=p.get b) : a=b := by
  induction p with
  | identity => exact h
  | seq p q ih ih' => exact ih' _ _ (ih _ _ h)
  | exchange Γ X Y Θ => exact At.swapBlocks_injective Γ X Y Θ a b h
  | reindex hF hU p ih=>cases hF;cases hU;exact ih a b h

theorem component (p : ExchangeScript P F U) (o : Op) {A : NormalForm P} (a : At U A) :
    (side P o).comp (p.arrow o) (Gentzen.component o a)=Gentzen.component o (p.get a) :=
  p.rewire.arrow_component o a

theorem left_count (p : ExchangeScript P F U) (f : G P U Δ) : (p.left f).cutCount=f.cutCount :=
  p.rewire.left_count f
theorem right_count (p : ExchangeScript P F U) (f : G P Γ U) : (p.right f).cutCount=f.cutCount :=
  p.rewire.right_count f
theorem left_atomized (p : ExchangeScript P F U) (f : G P U Δ) : (p.left f).Atomized↔f.Atomized :=
  p.rewire.left_atomized f
theorem right_atomized (p : ExchangeScript P F U) (f : G P Γ U) : (p.right f).Atomized↔f.Atomized :=
  p.rewire.right_atomized f
theorem left_denote (p : ExchangeScript P F U) (f : G P U Δ) :
    ofTerm (p.left f).denote=comp (p.arrow .conj) (ofTerm f.denote) := p.rewire.left_denote f
theorem right_denote (p : ExchangeScript P F U) (f : G P Γ U) :
    ofTerm (p.right f).denote=comp (ofTerm f.denote) (p.arrow .disj) := p.rewire.right_denote f

theorem bound_left {C : NormalForm P} {k : Nat} (p : ExchangeScript P F U) (f : G P U Δ)
    (E : At F C→Prop) (h : ContractionBound .left C k f (fun a=>E (p.get a))) :
    ContractionBound .left C k (p.left f) E := by
  induction p with
  | identity=>exact h
  | seq p q ih ih'=>exact ih (q.left f) E (ih' f (fun a=>E (p.get a)) h)
  | exchange Γ X Y Θ=>exact ContractionBound.exchangeL Γ X Y Θ Δ f E h
  | reindex hF hU p ih=>cases hF;cases hU;exact ih f E h

theorem bound_right {C : NormalForm P} {k : Nat} (p : ExchangeScript P F U) (f : G P Γ U)
    (E : At F C→Prop) (h : ContractionBound .right C k f (fun a=>E (p.get a))) :
    ContractionBound .right C k (p.right f) E := by
  induction p with
  | identity=>exact h
  | seq p q ih ih'=>exact ih (q.right f) E (ih' f (fun a=>E (p.get a)) h)
  | exchange Δ X Y Λ=>exact ContractionBound.exchangeR Δ X Y Λ Γ f E h
  | reindex hF hU p ih=>cases hF;cases hU;exact ih f E h
end ExchangeScript
end DosenPetric.Reduced.Gentzen
