module

public import DosenPetric.AtomicFactorization

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}
open Relations
namespace AtomicPorts

/-- The original occurrence block in a left-associated port object. -/
def embed (o : Op) (A : NormalForm P) : (ps : List P) → A.formula.Occ → (expand o A ps).formula.Occ
  | [], x => x
  | p :: ps, x => embed o (o.formula A (block o p)) ps (o.join A (block o p) (.inl x))

theorem embed_injective (o : Op) (A : NormalForm P) (ps : List P) {x y : A.formula.Occ}
    (h : embed o A ps x = embed o A ps y) : x = y := by
  induction ps generalizing A with
  | nil => exact h
  | cons p ps ih =>
    have hh := ih (o.formula A (block o p)) h
    cases o <;> exact Sum.inl.inj hh

theorem zeros_relation (o : Op) {A B : NormalForm P} (f : Term P A B) (ps : List P)
    (u : (expand o A ps).formula.Occ) (v : (expand o B ps).formula.Occ) :
    (zeros o f ps).relation u v ↔
      ∃ x y, u = embed o A ps x ∧ v = embed o B ps y ∧ f.relation x y := by
  induction ps generalizing A B with
  | nil => simp [zeros, mapTerm, embed]
  | cons p ps ih =>
    change (zeros o (.tensor o f (.zero (block o p))) ps).relation u v ↔ _
    rw [ih]
    cases o <;> simp [Term.relation, sumMap, empty, Sum.exists, embed, Op.join]

theorem mask_relation (o : Op) (A : NormalForm P) (ps : List P)
    (u v : (expand o A ps).formula.Occ) :
    (mask o A ps).relation u v ↔ ∃ x, u = embed o A ps x ∧ v = embed o A ps x := by
  change (zeros o (.id A) ps).relation u v ↔ _
  rw [zeros_relation]
  simp [Term.relation, graph]

theorem etaOne_relation (A : NormalForm P) (p : P) :
    (etaOne A p).relation = graph Sum.inl := eta_prefix_relation A p

theorem epsilonOne_relation (A : NormalForm P) (p : P)
    (u : (NormalForm.disj A (Atomic.epsilonObject p)).formula.Occ) (y : A.formula.Occ) :
    (epsilonOne A p).relation u y ↔ u = .inl y := epsilon_suffix_relation A p u y

theorem prefix_relation (A : NormalForm P) (ps : List P) :
    (etaPrefix A ps).relation = graph (embed .conj A ps) := by
  induction ps generalizing A with
  | nil => rfl
  | cons p ps ih =>
    change Relations.comp (etaOne A p).relation (etaPrefix (.conj A (Atomic.etaObject p)) ps).relation = _
    rw [etaOne_relation, ih, Relations.graph_comp]
    rfl

theorem suffix_relation (A : NormalForm P) (ps : List P)
    (u : (expand .disj A ps).formula.Occ) (y : A.formula.Occ) :
    (epsilonSuffix A ps).relation u y ↔ u = embed .disj A ps y := by
  induction ps generalizing A with
  | nil => rfl
  | cons p ps ih =>
    change (∃ z, (epsilonSuffix (.disj A (Atomic.epsilonObject p)) ps).relation u z ∧
      (epsilonOne A p).relation z y) ↔ _
    simp only [ih, epsilonOne_relation]
    simp [embed, Op.join]

/-- Explicit final zero factors. Auxiliary edges are removed at both endpoints. -/
def masked {A B : NormalForm P} {ps qs : List P}
    (m : Term P (expand .conj A ps) (expand .disj B qs)) : Term P (expand .conj A ps) (expand .disj B qs) :=
  .comp (mask .conj A ps) (.comp m (mask .disj B qs))

theorem masked_positive {A B : NormalForm P} {ps qs : List P}
    (m : Term P (expand .conj A ps) (expand .disj B qs)) (hm : m.Positive) :
    (masked m).Positive :=
  .comp (zeros_positive .conj (.id A) (.id A) ps)
    (.comp hm (zeros_positive .disj (.id B) (.id B) qs))

theorem masked_factor {A B : NormalForm P} {ps qs : List P} {t : Term P A B}
    (m : Term P (expand .conj A ps) (expand .disj B qs))
    (ht : ofTerm t = comp (ofTerm (etaPrefix A ps)) (comp (ofTerm m) (ofTerm (epsilonSuffix B qs)))) :
    ofTerm t = comp (ofTerm (etaPrefix A ps)) (comp (ofTerm (masked m)) (ofTerm (epsilonSuffix B qs))) := by
  simp only [masked, ofTerm_comp, Laws.assoc]
  rw [← Laws.assoc (ofTerm (etaPrefix A ps)), prefix_mask, mask_suffix]
  exact ht

theorem factor_relation {A B : NormalForm P} {ps qs : List P} {t : Term P A B}
    (m : Term P (expand .conj A ps) (expand .disj B qs))
    (ht : ofTerm t = comp (ofTerm (etaPrefix A ps)) (comp (ofTerm m) (ofTerm (epsilonSuffix B qs))))
    (x : A.formula.Occ) (y : B.formula.Occ) :
    t.relation x y ↔ m.relation (embed .conj A ps x) (embed .disj B qs y) := by
  have h := congrArg occurrenceMap ht
  rw [occurrence_comp, occurrence_comp] at h
  change t.relation = Relations.comp (etaPrefix A ps).relation (Relations.comp m.relation (epsilonSuffix B qs).relation) at h
  rw [prefix_relation] at h
  have hh := congrFun (congrFun h x) y
  simpa [Relations.comp, graph, suffix_relation] using hh

/-- Complete support, stronger than merely agreeing on the original occurrence block. -/
theorem masked_support {A B : NormalForm P} {ps qs : List P} {t : Term P A B}
    (m : Term P (expand .conj A ps) (expand .disj B qs))
    (ht : ofTerm t = comp (ofTerm (etaPrefix A ps)) (comp (ofTerm m) (ofTerm (epsilonSuffix B qs))))
    (u : (expand .conj A ps).formula.Occ) (v : (expand .disj B qs).formula.Occ) :
    (masked m).relation u v ↔ ∃ x y,
      u = embed .conj A ps x ∧ v = embed .disj B qs y ∧ t.relation x y := by
  change (∃ a, (mask .conj A ps).relation u a ∧ ∃ b, m.relation a b ∧ (mask .disj B qs).relation b v) ↔ _
  simp only [mask_relation]
  constructor
  · rintro ⟨a, ⟨x, hux, hax⟩, b, hab, y, hby, hvy⟩
    subst a; subst b
    exact ⟨x, y, hux, hvy, (factor_relation m ht x y).mpr hab⟩
  · rintro ⟨x, y, hux, hvy, hxy⟩
    exact ⟨embed .conj A ps x, ⟨x, hux, rfl⟩, embed .disj B qs y,
      (factor_relation m ht x y).mp hxy, y, rfl, hvy⟩

end AtomicPorts
/-- Individual factorization after the explicit zero masks have been included. -/
structure SupportedAtomicFactor {A B : NormalForm P} (t : Term P A B) extends AtomicFactor t where
  support : ∀ u v, middle.relation u v ↔ ∃ x y,
    u = AtomicPorts.embed .conj A etas x ∧ v = AtomicPorts.embed .disj B epsilons y ∧ t.relation x y

def supportedAtomicFactor {A B : NormalForm P} (t : Term P A B) : SupportedAtomicFactor t :=
  let s := atomicFactor t
  { etas := s.etas, epsilons := s.epsilons, middle := AtomicPorts.masked s.middle
    positive := AtomicPorts.masked_positive s.middle s.positive
    eta_list := s.eta_list, epsilon_list := s.epsilon_list
    eq := AtomicPorts.masked_factor s.middle s.eq
    support := AtomicPorts.masked_support s.middle s.eq }

end DosenPetric.Reduced
