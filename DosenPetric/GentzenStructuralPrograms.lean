module

public import DosenPetric.GentzenUnrestrictedExchangeReducers

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Finite derived programs in the existing unary structural rules. This is
an implementation of rule compositions; it adds no Gentzen constructor. -/
inductive StructuralProgram (P : Type u) : List (NormalForm P)→List (NormalForm P)→Type u where
  | identity (F) : StructuralProgram P F F
  | seq {F U K} : StructuralProgram P F U→StructuralProgram P U K→StructuralProgram P F K
  | exchange (Γ X Y Θ) : StructuralProgram P (Γ++Y++X++Θ) (Γ++X++Y++Θ)
  | thin (Γ Θ) (A : NormalForm P) : StructuralProgram P (Γ++A::Θ) (Γ++Θ)
  | contract (C gs Θ) : 2≤gs.length→StructuralProgram P (gaps gs++C::Θ) (repeated C gs++Θ)
  | reindex {F U K L} : F=K→U=L→StructuralProgram P F U→StructuralProgram P K L

namespace StructuralProgram
variable {F U K Δ : List (NormalForm P)}

def get : {F U : List (NormalForm P)}→StructuralProgram P F U→
    {A : NormalForm P}→At U A→At F A
  | _,_,.identity _,_,a=>a
  | _,_,.seq p q,_,a=>p.get (q.get a)
  | _,_,.exchange Γ X Y Θ,_,a=>a.swapBlocks Γ X Y Θ
  | _,_,.thin Γ Θ A,_,a=>(Route.thin Γ Θ A).get a
  | _,_,.contract C gs Θ _,_,a=>(copies C gs Θ).get a
  | _,_,.reindex hF hU p,_,a=>(p.get (a.cast hU.symm)).cast hF

def left : {F U : List (NormalForm P)}→StructuralProgram P F U→G P U Δ→G P F Δ
  | _,_,.identity _,f=>f
  | _,_,.seq p q,f=>p.left (q.left f)
  | _,_,.exchange Γ X Y Θ,f=>.exchangeL Γ X Y Θ Δ f
  | _,_,.thin Γ Θ A,f=>.thinL Γ Θ Δ A f
  | _,_,.contract C gs Θ hn,f=>.contractL C gs Θ Δ hn f
  | _,_,.reindex hF hU p,f=>(p.left (f.reindex hU.symm rfl)).reindex hF rfl

def right : {F U : List (NormalForm P)}→StructuralProgram P F U→G P Δ U→G P Δ F
  | _,_,.identity _,f=>f
  | _,_,.seq p q,f=>p.right (q.right f)
  | _,_,.exchange Γ X Y Θ,f=>.exchangeR Δ Γ X Y Θ f
  | _,_,.thin Γ Θ A,f=>.thinR Δ Γ Θ A f
  | _,_,.contract C gs Θ hn,f=>.contractR Δ C gs Θ hn f
  | _,_,.reindex hF hU p,f=>(p.right (f.reindex rfl hU.symm)).reindex rfl hF

def arrow (o : Op) : {F U : List (NormalForm P)}→StructuralProgram P F U→
    (side P o).Hom (fold o F) (fold o U)
  | _,_,.identity F=>(side P o).id (fold o F)
  | _,_,.seq p q=>(side P o).comp (p.arrow o) (q.arrow o)
  | _,_,.exchange Γ X Y Θ=>exchangeBack o Γ X Y Θ
  | _,_,.thin Γ Θ A=>(Route.thin Γ Θ A).sideArrow o
  | _,_,.contract C gs Θ _=>(copies C gs Θ).sideArrow o
  | _,_,.reindex hF hU p=>hF ▸ hU ▸ p.arrow o

theorem component (p : StructuralProgram P F U) (o : Op) {A : NormalForm P} (a : At U A) :
    (side P o).comp (p.arrow o) (Gentzen.component o a)=Gentzen.component o (p.get a) := by
  induction p with
  | identity=>exact (side P o).id_comp _
  | seq p q ih ih'=>rw [arrow,(side P o).assoc,ih',ih];rfl
  | exchange=>exact exchangeBack_component ..
  | thin=>exact Route.sideArrow_get ..
  | contract=>exact Route.sideArrow_get ..
  | reindex hF hU p ih=>cases hF;cases hU;exact ih a

theorem left_count (p : StructuralProgram P F U) (f : G P U Δ) : (p.left f).cutCount=f.cutCount := by
  induction p with
  | identity=>rfl
  | seq p q ih ih'=>exact (ih _).trans (ih' _)
  | exchange=>rfl
  | thin=>rfl
  | contract=>rfl
  | reindex hF hU p ih=>cases hF;cases hU;exact ih f

theorem right_count (p : StructuralProgram P F U) (f : G P Δ U) : (p.right f).cutCount=f.cutCount := by
  induction p with
  | identity=>rfl
  | seq p q ih ih'=>exact (ih _).trans (ih' _)
  | exchange=>rfl
  | thin=>rfl
  | contract=>rfl
  | reindex hF hU p ih=>cases hF;cases hU;exact ih f

theorem left_denote (p : StructuralProgram P F U) (f : G P U Δ) :
    ofTerm (p.left f).denote=comp (p.arrow .conj) (ofTerm f.denote) := by
  induction p with
  | identity=>exact (Laws.id_comp _).symm
  | seq p q ih ih'=>rw [left,ih,ih'];exact (Laws.assoc ..).symm
  | exchange=>rfl
  | thin=>rfl
  | contract=>rfl
  | reindex hF hU p ih=>cases hF;cases hU;exact ih f

theorem right_denote (p : StructuralProgram P F U) (f : G P Δ U) :
    ofTerm (p.right f).denote=comp (ofTerm f.denote) (p.arrow .disj) := by
  induction p with
  | identity=>exact (Laws.comp_id _).symm
  | seq p q ih ih'=>rw [right,ih,ih'];exact Laws.assoc ..
  | exchange=>rfl
  | thin=>rfl
  | contract=>rfl
  | reindex hF hU p ih=>cases hF;cases hU;exact ih f

def consFixed (A : NormalForm P) : {F U : List (NormalForm P)}→
    StructuralProgram P F U→StructuralProgram P (A::F) (A::U)
  | _,_,.identity F=>.identity (A::F)
  | _,_,.seq p q=>.seq (p.consFixed A) (q.consFixed A)
  | _,_,.exchange Γ X Y Θ=>.exchange (A::Γ) X Y Θ
  | _,_,.thin Γ Θ B=>.thin (A::Γ) Θ B
  | _,_,.contract C gs Θ hn=>
    match gs,hn with
    | H::hs,hn=>.contract C ((A::H)::hs) Θ hn
  | _,_,.reindex hF hU p=>.reindex (congrArg (List.cons A) hF) (congrArg (List.cons A) hU) (p.consFixed A)
end StructuralProgram
end DosenPetric.Reduced.Gentzen
