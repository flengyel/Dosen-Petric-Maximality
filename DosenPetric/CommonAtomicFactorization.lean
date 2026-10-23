module

public import DosenPetric.AtomicPortOccurrences

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}
open AtomicPorts

/-- Changing the original endpoints through positive maps leaves the port lists shared. -/
theorem AtomicFactor.remap {A B X Y : NormalForm P} {t : Term P A B}
    (s : AtomicFactor t) (l : Term P X A) (r : Term P B Y) :
    comp (ofTerm l) (comp (ofTerm t) (ofTerm r)) =
      comp (ofTerm (etaPrefix X s.etas))
        (comp (ofTerm (.comp (lift .conj l s.etas) (.comp s.middle (lift .disj r s.epsilons))))
          (ofTerm (epsilonSuffix Y s.epsilons))) := by
  have hl := prefix_natural (fun p => ofTerm (.id (block .conj p))) (ofTerm l) s.etas
  have hr := suffix_natural (fun p => ofTerm (.id (block .disj p))) (ofTerm r) s.epsilons
  rw [map_ofTerm] at hl hr
  calc
    comp (ofTerm l) (comp (ofTerm t) (ofTerm r)) =
      comp (comp (ofTerm l) (ofTerm (etaPrefix A s.etas)))
        (comp (ofTerm s.middle) (comp (ofTerm (epsilonSuffix B s.epsilons)) (ofTerm r))) := by
          rw [s.eq]; simp only [Laws.assoc]
    _ = comp (comp (ofTerm (etaPrefix X s.etas)) (ofTerm (lift .conj l s.etas)))
        (comp (ofTerm s.middle) (comp (ofTerm (lift .disj r s.epsilons)) (ofTerm (epsilonSuffix Y s.epsilons)))) := by
          rw [← hl, ← hr]; rfl
    _ = _ := by simp only [ofTerm_comp, Laws.assoc]

/-- Shared etaPrefix/epsilonSuffix and positive raw middle terms, including all endpoint zero masks. -/
structure CommonAtomicFactor {A B : NormalForm P} (t₁ t₂ : Term P A B) where
  etas : List P
  epsilons : List P
  eta_list : etas = t₁.etaLabels ++ t₂.etaLabels
  epsilon_list : epsilons = t₁.epsilonLabels ++ t₂.epsilonLabels
  middle₁ : Term P (expand .conj A etas) (expand .disj B epsilons)
  middle₂ : Term P (expand .conj A etas) (expand .disj B epsilons)
  positive₁ : middle₁.Positive
  positive₂ : middle₂.Positive
  eq₁ : ofTerm t₁ = comp (ofTerm (etaPrefix A etas)) (comp (ofTerm middle₁) (ofTerm (epsilonSuffix B epsilons)))
  eq₂ : ofTerm t₂ = comp (ofTerm (etaPrefix A etas)) (comp (ofTerm middle₂) (ofTerm (epsilonSuffix B epsilons)))
  support₁ : ∀ u v, middle₁.relation u v ↔ ∃ x y,
    u = embed .conj A etas x ∧ v = embed .disj B epsilons y ∧ t₁.relation x y
  support₂ : ∀ u v, middle₂.relation u v ↔ ∃ x y,
    u = embed .conj A etas x ∧ v = embed .disj B epsilons y ∧ t₂.relation x y

/-- One extraction of the tensor pair gives the common concatenated occurrence lists.
Diagonal/projection naturality supplies the padding, without testing label equality. -/
def commonAtomicFactor {A B : NormalForm P} (t₁ t₂ : Term P A B) : CommonAtomicFactor t₁ t₂ := by
  let s := atomicFactor (.tensor .conj t₁ t₂)
  let m₁ := Term.comp (lift .conj (.diag A) s.etas) (.comp s.middle (lift .disj (.fst B B) s.epsilons))
  let m₂ := Term.comp (lift .conj (.diag A) s.etas) (.comp s.middle (lift .disj (.snd B B) s.epsilons))
  have hm₁ : m₁.Positive := .comp (lift_positive _ _ (.diag A) _)
    (.comp s.positive (lift_positive _ _ (.fst B B) _))
  have hm₂ : m₂.Positive := .comp (lift_positive _ _ (.diag A) _)
    (.comp s.positive (lift_positive _ _ (.snd B B) _))
  have h₁ : ofTerm t₁ = comp (ofTerm (etaPrefix A s.etas)) (comp (ofTerm m₁) (ofTerm (epsilonSuffix B s.epsilons))) := by
    have h := s.remap (.diag A) (.fst B B)
    have hp : comp (diag A) (comp (tensor .conj (ofTerm t₁) (ofTerm t₂)) (fst B B)) = ofTerm t₁ := by
      rw [← Laws.assoc]
      exact (conjDiagonal P).pair_fst (ofTerm t₁) (ofTerm t₂)
    exact hp.symm.trans h
  have h₂ : ofTerm t₂ = comp (ofTerm (etaPrefix A s.etas)) (comp (ofTerm m₂) (ofTerm (epsilonSuffix B s.epsilons))) := by
    have h := s.remap (.diag A) (.snd B B)
    have hp : comp (diag A) (comp (tensor .conj (ofTerm t₁) (ofTerm t₂)) (snd B B)) = ofTerm t₂ := by
      rw [← Laws.assoc]
      exact (conjDiagonal P).pair_snd (ofTerm t₁) (ofTerm t₂)
    exact hp.symm.trans h
  exact { etas := s.etas, epsilons := s.epsilons
          eta_list := s.eta_list.symm, epsilon_list := s.epsilon_list.symm
          middle₁ := masked m₁, middle₂ := masked m₂
          positive₁ := masked_positive m₁ hm₁, positive₂ := masked_positive m₂ hm₂
          eq₁ := masked_factor m₁ h₁, eq₂ := masked_factor m₂ h₂
          support₁ := masked_support m₁ h₁, support₂ := masked_support m₂ h₂ }

namespace CommonAtomicFactor
variable {A B : NormalForm P} {t₁ t₂ : Term P A B}

def input (s : CommonAtomicFactor t₁ t₂) := expand .conj A s.etas
def output (s : CommonAtomicFactor t₁ t₂) := expand .disj B s.epsilons
def before (s : CommonAtomicFactor t₁ t₂) : Hom A s.input := ofTerm (etaPrefix A s.etas)
def after (s : CommonAtomicFactor t₁ t₂) : Hom s.output B := ofTerm (epsilonSuffix B s.epsilons)
def embedA (s : CommonAtomicFactor t₁ t₂) := embed .conj A s.etas
def embedB (s : CommonAtomicFactor t₁ t₂) := embed .disj B s.epsilons

theorem embedA_injective (s : CommonAtomicFactor t₁ t₂) {x y : A.formula.Occ}
    (h : s.embedA x = s.embedA y) : x = y := embed_injective .conj A s.etas h

theorem embedB_injective (s : CommonAtomicFactor t₁ t₂) {x y : B.formula.Occ}
    (h : s.embedB x = s.embedB y) : x = y := embed_injective .disj B s.epsilons h

theorem embedded₁ (s : CommonAtomicFactor t₁ t₂) (x : A.formula.Occ) (y : B.formula.Occ) :
    s.middle₁.relation (s.embedA x) (s.embedB y) ↔ t₁.relation x y := by
  rw [s.support₁]
  constructor
  · rintro ⟨a, b, ha, hb, h⟩
    have hx := embed_injective .conj A s.etas ha
    have hy := embed_injective .disj B s.epsilons hb
    cases hx; cases hy; exact h
  · intro h; exact ⟨x, y, rfl, rfl, h⟩

theorem embedded₂ (s : CommonAtomicFactor t₁ t₂) (x : A.formula.Occ) (y : B.formula.Occ) :
    s.middle₂.relation (s.embedA x) (s.embedB y) ↔ t₂.relation x y := by
  rw [s.support₂]
  constructor
  · rintro ⟨a, b, ha, hb, h⟩
    have hx := embed_injective .conj A s.etas ha
    have hy := embed_injective .disj B s.epsilons hb
    cases hx; cases hy; exact h
  · intro h; exact ⟨x, y, rfl, rfl, h⟩

theorem relations_equal (s : CommonAtomicFactor t₁ t₂) (h : t₁.relation = t₂.relation) :
    s.middle₁.relation = s.middle₂.relation := by
  funext u v
  apply propext
  rw [s.support₁, s.support₂, h]

end CommonAtomicFactor

/-- Conditional transfer; the positive coherence premise is not supplied here. -/
theorem faithful_of_positive_coherence (hC : PositiveCoherence P) : Faithful P := by
  intro A B f g h
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g =>
  let s := commonAtomicFactor f g
  have hm := hC s.middle₁ s.middle₂ s.positive₁ s.positive₂ (s.relations_equal h)
  change ofTerm f = ofTerm g
  rw [s.eq₁, s.eq₂, hm]

end DosenPetric.Reduced
