module

public import DosenPetric.GentzenAnchoredRouteFactor

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace StructuralProgram
variable {F U : List (NormalForm P)}

/-- Every thinning in the program inserts an atomic formula. -/
def Atomic : {F U : List (NormalForm P)} → StructuralProgram P F U → Prop
  | _,_,.identity _ | _,_,.exchange _ _ _ _ | _,_,.contract _ _ _ _ => True
  | _,_,.seq p q => p.Atomic ∧ q.Atomic
  | _,_,.thin _ _ A => AtomicFormula A
  | _,_,.reindex _ _ p => p.Atomic

theorem atomic_seq {K : List (NormalForm P)} (p : StructuralProgram P F U)
    (q : StructuralProgram P U K) (hp : p.Atomic) (hq : q.Atomic) :
    (p.seq q).Atomic := ⟨hp,hq⟩

theorem atomic_reindex {K L : List (NormalForm P)} (p : StructuralProgram P F U)
    (hF : F=K) (hU : U=L) (hp : p.Atomic) : (p.reindex hF hU).Atomic := hp

theorem left_cutFree {Δ : List (NormalForm P)} (p : StructuralProgram P F U)
    (f : G P U Δ) (hf : f.CutFree) : (p.left f).CutFree := by
  change (p.left f).cutCount=0
  rw [p.left_count]
  exact hf

theorem right_cutFree {Δ : List (NormalForm P)} (p : StructuralProgram P F U)
    (f : G P Δ U) (hf : f.CutFree) : (p.right f).CutFree := by
  change (p.right f).cutCount=0
  rw [p.right_count]
  exact hf

theorem atomic_consFixed (p : StructuralProgram P F U) (A : NormalForm P)
    (h : p.Atomic) : (p.consFixed A).Atomic := by
  induction p with
  | identity | exchange => trivial
  | seq p q ih ih' => exact ⟨ih h.1,ih' h.2⟩
  | thin => exact h
  | contract C gs Θ hn =>
    cases gs with
    | nil => change 2 ≤ 0 at hn; omega
    | cons => trivial
  | reindex hF hU p ih => exact ih h

theorem left_atomized {Δ : List (NormalForm P)} (p : StructuralProgram P F U)
    (hp : p.Atomic) (f : G P U Δ) (hf : f.Atomized) : (p.left f).Atomized := by
  induction p with
  | identity => exact hf
  | seq p q ih ih' => exact ih hp.1 _ (ih' hp.2 _ hf)
  | exchange | contract => exact hf
  | thin => exact ⟨hp,hf⟩
  | reindex hF hU p ih => cases hF; cases hU; exact ih hp f hf

theorem right_atomized {Δ : List (NormalForm P)} (p : StructuralProgram P F U)
    (hp : p.Atomic) (f : G P Δ U) (hf : f.Atomized) : (p.right f).Atomized := by
  induction p with
  | identity => exact hf
  | seq p q ih ih' => exact ih hp.1 _ (ih' hp.2 _ hf)
  | exchange | contract => exact hf
  | thin => exact ⟨hp,hf⟩
  | reindex hF hU p ih => cases hF; cases hU; exact ih hp f hf
end StructuralProgram

namespace ExchangeScript
variable {F U : List (NormalForm P)}

def program : {F U : List (NormalForm P)} → ExchangeScript P F U → StructuralProgram P F U
  | _,_,.identity F => .identity F
  | _,_,.seq p q => .seq p.program q.program
  | _,_,.exchange Γ X Y Θ => .exchange Γ X Y Θ
  | _,_,.reindex hF hU p => .reindex hF hU p.program

theorem program_get (p : ExchangeScript P F U) {A : NormalForm P} (a : At U A) :
    p.program.get a = p.get a := by
  induction p with
  | identity | exchange => rfl
  | seq p q ih ih' => exact (congrArg p.program.get (ih' a)).trans (ih (q.get a))
  | reindex hF hU p ih => cases hF; cases hU; exact ih a

theorem program_atomic (p : ExchangeScript P F U) : p.program.Atomic := by
  induction p with
  | identity | exchange => trivial
  | seq p q ih ih' => exact ⟨ih,ih'⟩
  | reindex hF hU p ih => exact ih
end ExchangeScript

namespace ContractionSelection
variable {F K : List (NormalForm P)} {C : NormalForm P}

/-- Singleton selections perform only equality transport. -/
noncomputable def programAll (p : ContractionSelection C F K) : StructuralProgram P K F :=
  if h : 2 ≤ p.arity then p.program h
  else (StructuralProgram.identity F).reindex
    (p.singleton_endpoints (by have hp := p.arity_pos; omega)) rfl

theorem programAll_get (p : ContractionSelection C F K) {A : NormalForm P} (a : At F A) :
    p.programAll.get a = p.route.get a := by
  unfold programAll
  split
  · exact p.program_get _ a
  · exact (p.singleton_get (by have hp := p.arity_pos; omega) a).symm

theorem programAll_atomic (p : ContractionSelection C F K) : p.programAll.Atomic := by
  unfold programAll
  split <;> trivial
end ContractionSelection

namespace Route
variable {K F : List (NormalForm P)}

/-- An unused position of the lower context has an atomic label. Usage refers
to its tag, even when other positions have the same formula. -/
def AtomicOmissions (r : Route K F) : Prop :=
  ∀ {A : NormalForm P} (a : At K A), (¬ ∃ b : At F A, r.get b = a) → AtomicFormula A
end Route
end DosenPetric.Reduced.Gentzen
