module

public import DosenPetric.PositiveFragment

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}

inductive Atomic (P : Type u) where
  | eta (p : P)
  | epsilon (p : P)

namespace Atomic

@[reducible] def etaObject (p : P) : NormalForm P := .disj (.lit (.neg p)) (.lit (.pos p))
@[reducible] def epsilonObject (p : P) : NormalForm P := .conj (.lit (.pos p)) (.lit (.neg p))
@[reducible] def source : Atomic P → NormalForm P
  | .eta _ => .top
  | .epsilon p => epsilonObject p
@[reducible] def target : Atomic P → NormalForm P
  | .eta p => etaObject p
  | .epsilon _ => .bot
@[reducible] def term : (a : Atomic P) → Term P a.source a.target
  | .eta p => .eta p
  | .epsilon p => .epsilon p
def etas : Atomic P → List P | .eta p => [p] | .epsilon _ => []
def epsilons : Atomic P → List P | .eta _ => [] | .epsilon p => [p]

end Atomic

/-- A first atomic occurrence, with a positive prefix and its exact remaining occurrence lists. -/
structure AtomicSplit {A B : NormalForm P} (a : Atomic P) (t : Term P A B) where
  context : Context P
  before : Term P A (context.plug a.source)
  after : Term P (context.plug a.target) B
  before_positive : before.Positive
  eq : ofTerm t = comp (ofTerm before) (comp (context.map (ofTerm a.term)) (ofTerm after))
  etas : t.etaLabels = a.etas ++ after.etaLabels
  epsilons : t.epsilonLabels = a.epsilons ++ after.epsilonLabels

namespace AtomicSplit
variable {a : Atomic P} {A B C : NormalForm P}

def thenTerm {f : Term P A B} (s : AtomicSplit a f) (g : Term P B C) : AtomicSplit a (.comp f g) where
  context := s.context
  before := s.before
  after := .comp s.after g
  before_positive := s.before_positive
  eq := by
    change comp (ofTerm f) (ofTerm g) = _
    rw [s.eq]; simp only [Laws.assoc]; rfl
  etas := by simp only [Term.etaLabels, s.etas, List.append_assoc]
  epsilons := by simp only [Term.epsilonLabels, s.epsilons, List.append_assoc]

def preTerm (f : Term P A B) (hf : f.Positive) {g : Term P B C} (s : AtomicSplit a g) :
    AtomicSplit a (.comp f g) where
  context := s.context
  before := .comp f s.before
  after := s.after
  before_positive := .comp hf s.before_positive
  eq := by
    change comp (ofTerm f) (ofTerm g) = _
    rw [s.eq]; exact (Laws.assoc ..).symm
  etas := by simp only [Term.etaLabels, hf.etaLabels, List.nil_append, s.etas]
  epsilons := by simp only [Term.epsilonLabels, hf.epsilonLabels, List.nil_append, s.epsilons]

def tensorLeft (o : Op) {A B C D : NormalForm P} {f : Term P A C}
    (s : AtomicSplit a f) (g : Term P B D) : AtomicSplit a (.tensor o f g) where
  context := .right o s.context B
  before := .tensor o s.before (.id B)
  after := .tensor o s.after g
  before_positive := .tensor o s.before_positive (.id B)
  eq := by
    change tensor o (ofTerm f) (ofTerm g) =
      comp (tensor o (ofTerm s.before) (id B))
        (comp ((Context.right o s.context B).map (ofTerm a.term)) (tensor o (ofTerm s.after) (ofTerm g)))
    rw [Context.map_right, s.eq]
    simp only [Laws.tensor_comp, Laws.id_comp]
  etas := by simp only [Term.etaLabels, s.etas, List.append_assoc]
  epsilons := by simp only [Term.epsilonLabels, s.epsilons, List.append_assoc]

def tensorRight (o : Op) {A B C D : NormalForm P} (f : Term P A C) (hf : f.Positive)
    {g : Term P B D} (s : AtomicSplit a g) : AtomicSplit a (.tensor o f g) where
  context := .left o A s.context
  before := .tensor o (.id A) s.before
  after := .tensor o f s.after
  before_positive := .tensor o (.id A) s.before_positive
  eq := by
    change tensor o (ofTerm f) (ofTerm g) =
      comp (tensor o (id A) (ofTerm s.before))
        (comp ((Context.left o A s.context).map (ofTerm a.term)) (tensor o (ofTerm f) (ofTerm s.after)))
    rw [Context.map_left, s.eq]
    simp only [Laws.tensor_comp, Laws.id_comp]
  etas := by simp only [Term.etaLabels, hf.etaLabels, List.nil_append, s.etas]
  epsilons := by simp only [Term.epsilonLabels, hf.epsilonLabels, List.nil_append, s.epsilons]

end AtomicSplit

namespace Term

inductive AtomicView {A B : NormalForm P} (t : Term P A B) where
  | positive (h : t.Positive)
  | split (a : Atomic P) (s : AtomicSplit a t)

/-- Structural recursion selects a single syntactic occurrence, never a variable-label match. -/
def atomicView : {A B : NormalForm P} → (t : Term P A B) → AtomicView t
  | _, _, .comp f g => match f.atomicView with
    | .split a s => .split a (s.thenTerm g)
    | .positive hf => match g.atomicView with
      | .split a s => .split a (s.preTerm f hf)
      | .positive hg => .positive (.comp hf hg)
  | _, _, .tensor o f g => match f.atomicView with
    | .split a s => .split a (s.tensorLeft o g)
    | .positive hf => match g.atomicView with
      | .split a s => .split a (s.tensorRight o f hf)
      | .positive hg => .positive (.tensor o hf hg)
  | _, _, .eta p => .split (.eta p) {
      context := .hole, before := .id .top, after := .id (Atomic.etaObject p)
      before_positive := .id _
      eq := by
        change ofTerm (.eta p) = Reduced.comp (Reduced.id .top) (Reduced.comp (Context.hole.map (ofTerm (.eta p))) (Reduced.id (Atomic.etaObject p)))
        rw [Context.map_hole, Laws.id_comp, Laws.comp_id] <;> rfl
      etas := rfl, epsilons := rfl }
  | _, _, .epsilon p => .split (.epsilon p) {
      context := .hole, before := .id (Atomic.epsilonObject p), after := .id .bot
      before_positive := .id _
      eq := by
        change ofTerm (.epsilon p) = Reduced.comp (Reduced.id (Atomic.epsilonObject p)) (Reduced.comp (Context.hole.map (ofTerm (.epsilon p))) (Reduced.id .bot))
        rw [Context.map_hole, Laws.id_comp, Laws.comp_id] <;> rfl
      etas := rfl, epsilons := rfl }
  | _, _, .id A => .positive (.id A)
  | _, _, .assocR o A B C => .positive (.assocR o A B C)
  | _, _, .assocL o A B C => .positive (.assocL o A B C)
  | _, _, .swap o A B => .positive (.swap o A B)
  | _, _, .diag A => .positive (.diag A)
  | _, _, .codiag A => .positive (.codiag A)
  | _, _, .fst A B => .positive (.fst A B)
  | _, _, .snd A B => .positive (.snd A B)
  | _, _, .inl A B => .positive (.inl A B)
  | _, _, .inr A B => .positive (.inr A B)
  | _, _, .rightOut o A => .positive (.rightOut o A)
  | _, _, .rightIn o A => .positive (.rightIn o A)
  | _, _, .leftOut o A => .positive (.leftOut o A)
  | _, _, .leftIn o A => .positive (.leftIn o A)
  | _, _, .mix A B => .positive (.mix A B)
  | _, _, .dist A B C => .positive (.dist A B C)
  | _, _, .zero A => .positive (.zero A)

end Term
end DosenPetric.Reduced
