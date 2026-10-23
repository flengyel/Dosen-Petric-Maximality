module

public import DosenPetric.ContextOccurrences

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}
namespace Term

/-- The eta/epsilon-free arrow grammar; signed literal objects are unrestricted. -/
inductive Positive : {A B : NormalForm P} → Term P A B → Prop where
  | id (A) : Positive (.id A)
  | comp {A B C} {f : Term P A B} {g : Term P B C} : Positive f → Positive g → Positive (.comp f g)
  | tensor (o) {A B C D} {f : Term P A C} {g : Term P B D} :
      Positive f → Positive g → Positive (.tensor o f g)
  | assocR (o A B C) : Positive (.assocR o A B C)
  | assocL (o A B C) : Positive (.assocL o A B C)
  | swap (o A B) : Positive (.swap o A B)
  | diag (A) : Positive (.diag A)
  | codiag (A) : Positive (.codiag A)
  | fst (A B) : Positive (.fst A B)
  | snd (A B) : Positive (.snd A B)
  | inl (A B) : Positive (.inl A B)
  | inr (A B) : Positive (.inr A B)
  | rightOut (o A) : Positive (.rightOut o A)
  | rightIn (o A) : Positive (.rightIn o A)
  | leftOut (o A) : Positive (.leftOut o A)
  | leftIn (o A) : Positive (.leftIn o A)
  | mix (A B) : Positive (.mix A B)
  | dist (A B C) : Positive (.dist A B C)
  | zero (A) : Positive (.zero A)

/-- Lists record syntactic occurrences in traversal order, without deduplication. -/
def etaLabels : {A B : NormalForm P} → Term P A B → List P
  | _, _, .comp f g => f.etaLabels ++ g.etaLabels
  | _, _, .tensor _ f g => f.etaLabels ++ g.etaLabels
  | _, _, .eta p => [p]
  | _, _, _ => []

def epsilonLabels : {A B : NormalForm P} → Term P A B → List P
  | _, _, .comp f g => f.epsilonLabels ++ g.epsilonLabels
  | _, _, .tensor _ f g => f.epsilonLabels ++ g.epsilonLabels
  | _, _, .epsilon p => [p]
  | _, _, _ => []

def atomicCount {A B : NormalForm P} (t : Term P A B) : Nat :=
  t.etaLabels.length + t.epsilonLabels.length

theorem Positive.etaLabels {A B : NormalForm P} {t : Term P A B} (h : t.Positive) : t.etaLabels = [] := by
  induction h <;> simp_all [Term.etaLabels]

theorem Positive.epsilonLabels {A B : NormalForm P} {t : Term P A B} (h : t.Positive) : t.epsilonLabels = [] := by
  induction h <;> simp_all [Term.epsilonLabels]

theorem positive_of_labels {A B : NormalForm P} (t : Term P A B)
    (he : t.etaLabels = []) (hf : t.epsilonLabels = []) : t.Positive := by
  induction t with
  | comp f g ih ih' =>
    simp only [etaLabels, List.append_eq_nil_iff] at he
    simp only [epsilonLabels, List.append_eq_nil_iff] at hf
    exact .comp (ih he.1 hf.1) (ih' he.2 hf.2)
  | tensor o f g ih ih' =>
    simp only [etaLabels, List.append_eq_nil_iff] at he
    simp only [epsilonLabels, List.append_eq_nil_iff] at hf
    exact .tensor o (ih he.1 hf.1) (ih' he.2 hf.2)
  | eta p => cases he
  | epsilon p => cases hf
  | id A => exact .id A
  | assocR o A B C => exact .assocR o A B C
  | assocL o A B C => exact .assocL o A B C
  | swap o A B => exact .swap o A B
  | diag A => exact .diag A
  | codiag A => exact .codiag A
  | fst A B => exact .fst A B
  | snd A B => exact .snd A B
  | inl A B => exact .inl A B
  | inr A B => exact .inr A B
  | rightOut o A => exact .rightOut o A
  | rightIn o A => exact .rightIn o A
  | leftOut o A => exact .leftOut o A
  | leftIn o A => exact .leftIn o A
  | mix A B => exact .mix A B
  | dist A B C => exact .dist A B C
  | zero A => exact .zero A

theorem Positive.distRight (A B C : NormalForm P) : (distRight A B C).Positive :=
  .comp (.swap ..) (.comp (.tensor _ (.id _) (.swap ..))
    (.comp (.dist ..) (.comp (.tensor _ (.swap ..) (.id _)) (.swap ..))))

end Term

namespace Context

theorem gConj_positive (K : Context P) (B : NormalForm P) : (K.gConj B).Positive := by
  induction K with
  | hole => exact .leftOut ..
  | left o C K ih =>
    cases o with
    | conj => exact .comp (.assocL ..) (.tensor _ (.id _) ih)
    | disj => exact .comp (.distRight ..) (.tensor _ (.id _) ih)
  | right o K C ih =>
    cases o with
    | conj => exact .comp (.swap ..) (.comp (.assocR ..)
        (.comp (.tensor _ (.swap ..) (.id _)) (.tensor _ ih (.id _))))
    | disj => exact .comp (.swap ..) (.comp (.dist ..)
        (.comp (.tensor _ (.swap ..) (.id _)) (.tensor _ ih (.id _))))

theorem gDisj_positive (K : Context P) (B : NormalForm P) : (K.gDisj B).Positive := by
  induction K with
  | hole => exact .leftIn ..
  | left o C K ih =>
    cases o with
    | disj => exact .comp (.tensor _ (.id _) ih) (.assocR ..)
    | conj => exact .comp (.tensor _ (.id _) ih) (.dist ..)
  | right o K C ih =>
    cases o with
    | disj => exact .comp (.tensor _ ih (.id _)) (.comp (.tensor _ (.swap ..) (.id _)) (.comp (.assocL ..) (.swap ..)))
    | conj => exact .comp (.tensor _ ih (.id _)) (.comp (.tensor _ (.swap ..) (.id _)) (.comp (.distRight ..) (.swap ..)))

end Context

/-- The only coherence input needed after common factorization. Equality is in Reduced.Hom. -/
def PositiveCoherence (P : Type u) : Prop :=
  ∀ {A B : NormalForm P} (f g : Term P A B), f.Positive → g.Positive →
    f.relation = g.relation → ofTerm f = ofTerm g

end DosenPetric.Reduced
