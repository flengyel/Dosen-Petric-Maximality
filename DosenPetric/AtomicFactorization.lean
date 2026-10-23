module

public import DosenPetric.AtomicPorts

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}
namespace AtomicSplit
variable {A B : NormalForm P} {t : Term P A B} {p : P}

def etaRemainder (s : AtomicSplit (.eta p) t) : Term P (.conj A (Atomic.etaObject p)) B :=
  .comp (.tensor .conj s.before (.zero (Atomic.etaObject p)))
    (.comp (s.context.gConj (Atomic.etaObject p)) s.after)

def epsilonRemainder (s : AtomicSplit (.epsilon p) t) : Term P A (.disj B (Atomic.epsilonObject p)) :=
  .comp s.before (.comp (s.context.gDisj (Atomic.epsilonObject p))
    (.tensor .disj s.after (.zero (Atomic.epsilonObject p))))

theorem eta_factor (s : AtomicSplit (.eta p) t) :
    ofTerm t = comp (ofTerm (AtomicPorts.etaOne A p)) (ofTerm s.etaRemainder) := by
  change ofTerm t = comp (ofTerm (AtomicPorts.etaOne A p))
    (comp (tensor .conj (ofTerm s.before) (zero (Atomic.etaObject p)))
      (comp (ofTerm (s.context.gConj (Atomic.etaObject p))) (ofTerm s.after)))
  rw [s.eq, ← Laws.assoc, s.context.gEta_comp (ofTerm (.eta p)) (ofTerm s.before)]
  simp only [AtomicPorts.etaOne, ofTerm_comp, ofTerm_tensor, ofTerm_id, Laws.assoc]
  rfl

theorem epsilon_factor (s : AtomicSplit (.epsilon p) t) :
    ofTerm t = comp (ofTerm s.epsilonRemainder) (ofTerm (AtomicPorts.epsilonOne B p)) := by
  change ofTerm t = comp
    (comp (ofTerm s.before) (comp (ofTerm (s.context.gDisj (Atomic.epsilonObject p)))
      (tensor .disj (ofTerm s.after) (zero (Atomic.epsilonObject p))))) _
  rw [s.eq, s.context.gEpsilon_comp (ofTerm (.epsilon p)) (ofTerm s.after)]
  simp only [Laws.assoc]
  rfl

theorem etaRemainder_etas (s : AtomicSplit (.eta p) t) : s.etaRemainder.etaLabels = s.after.etaLabels := by
  simp only [etaRemainder, Term.etaLabels, s.before_positive.etaLabels,
    (s.context.gConj_positive (Atomic.etaObject p)).etaLabels, List.nil_append]

theorem etaRemainder_epsilons (s : AtomicSplit (.eta p) t) : s.etaRemainder.epsilonLabels = s.after.epsilonLabels := by
  simp only [etaRemainder, Term.epsilonLabels, s.before_positive.epsilonLabels,
    (s.context.gConj_positive (Atomic.etaObject p)).epsilonLabels, List.nil_append]

theorem epsilonRemainder_etas (s : AtomicSplit (.epsilon p) t) : s.epsilonRemainder.etaLabels = s.after.etaLabels := by
  simp only [epsilonRemainder, Term.etaLabels, s.before_positive.etaLabels,
    (s.context.gDisj_positive (Atomic.epsilonObject p)).etaLabels, List.nil_append, List.append_nil]

theorem epsilonRemainder_epsilons (s : AtomicSplit (.epsilon p) t) : s.epsilonRemainder.epsilonLabels = s.after.epsilonLabels := by
  simp only [epsilonRemainder, Term.epsilonLabels, s.before_positive.epsilonLabels,
    (s.context.gDisj_positive (Atomic.epsilonObject p)).epsilonLabels, List.nil_append, List.append_nil]

theorem etaRemainder_lt (s : AtomicSplit (.eta p) t) : s.etaRemainder.atomicCount < t.atomicCount := by
  have h : t.atomicCount = s.etaRemainder.atomicCount + 1 := by
    simp [Term.atomicCount, s.etas, s.epsilons, Atomic.etas, Atomic.epsilons,
      etaRemainder_etas, etaRemainder_epsilons, Nat.add_comm, Nat.add_left_comm]
  rw [h]; exact Nat.lt_succ_self _

theorem epsilonRemainder_lt (s : AtomicSplit (.epsilon p) t) : s.epsilonRemainder.atomicCount < t.atomicCount := by
  have h : t.atomicCount = s.epsilonRemainder.atomicCount + 1 := by
    simp [Term.atomicCount, s.etas, s.epsilons, Atomic.etas, Atomic.epsilons,
      epsilonRemainder_etas, epsilonRemainder_epsilons, Nat.add_assoc, Nat.add_comm]
  rw [h]; exact Nat.lt_succ_self _

end AtomicSplit

/-- Initial positive middle term, before the final common padding and endpoint masks. -/
structure AtomicFactor {A B : NormalForm P} (t : Term P A B) where
  etas : List P
  epsilons : List P
  middle : Term P (AtomicPorts.expand .conj A etas) (AtomicPorts.expand .disj B epsilons)
  positive : middle.Positive
  eta_list : t.etaLabels = etas
  epsilon_list : t.epsilonLabels = epsilons
  eq : ofTerm t = comp (ofTerm (AtomicPorts.etaPrefix A etas))
    (comp (ofTerm middle) (ofTerm (AtomicPorts.epsilonSuffix B epsilons)))

/-- Each call removes one atomic occurrence, including repetitions of the same letter. -/
def atomicFactor : {A B : NormalForm P} → (t : Term P A B) → AtomicFactor t
  | A, B, t => by
    cases t.atomicView with
    | positive h =>
      exact { etas := [], epsilons := [], middle := t, positive := h
              eta_list := h.etaLabels, epsilon_list := h.epsilonLabels
              eq := by change ofTerm t = comp (id A) (comp (ofTerm t) (id B)); rw [Laws.id_comp, Laws.comp_id] }
    | split a s =>
      cases a with
      | eta p =>
        let r := atomicFactor s.etaRemainder
        exact { etas := p :: r.etas, epsilons := r.epsilons, middle := r.middle, positive := r.positive
                eta_list := by rw [s.etas]; change p :: s.after.etaLabels = _; rw [← s.etaRemainder_etas, r.eta_list]
                epsilon_list := by rw [s.epsilons]; change s.after.epsilonLabels = _; rw [← s.etaRemainder_epsilons, r.epsilon_list]
                eq := by rw [s.eta_factor, r.eq]; change _ = comp (comp (ofTerm (AtomicPorts.etaOne A p)) (ofTerm (AtomicPorts.etaPrefix _ r.etas))) _; rw [Laws.assoc] }
      | epsilon p =>
        let r := atomicFactor s.epsilonRemainder
        exact { etas := r.etas, epsilons := p :: r.epsilons, middle := r.middle, positive := r.positive
                eta_list := by rw [s.etas]; change s.after.etaLabels = _; rw [← s.epsilonRemainder_etas, r.eta_list]
                epsilon_list := by rw [s.epsilons]; change p :: s.after.epsilonLabels = _; rw [← s.epsilonRemainder_epsilons, r.epsilon_list]
                eq := by rw [s.epsilon_factor, r.eq]; change _ = comp _ (comp _ (comp (ofTerm (AtomicPorts.epsilonSuffix _ r.epsilons)) (ofTerm (AtomicPorts.epsilonOne B p)))); simp only [Laws.assoc] }
termination_by _ _ t => t.atomicCount
decreasing_by
  · exact s.etaRemainder_lt
  · exact s.epsilonRemainder_lt

end DosenPetric.Reduced
