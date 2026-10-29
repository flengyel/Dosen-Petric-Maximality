module

public import DosenPetric.GentzenPurePositiveCoherence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Disjunctive normal form, allowing both constants inside pure conjunctions. -/
inductive DNF : NormalForm P → Prop where
  | pure {A} : Pure .conj A → DNF A
  | disj {A B} : DNF A → DNF B → DNF (.disj A B)

/-- Conjunctive normal form with pure disjunctive components. -/
inductive CNF : NormalForm P → Prop where
  | pure {A} : Pure .disj A → CNF A
  | conj {A B} : CNF A → CNF B → CNF (.conj A B)

/-- Restricted coherence for normal-form endpoints, derived by the actual
coproduct and product universal properties from finite atomic normalization. -/
theorem normal_positive_coherence {A B : NormalForm P} (d : DNF A) (c : CNF B)
    (f g : Term P A B) (hf : f.Positive) (hg : g.Positive)
    (h : f.relation = g.relation) : ofTerm f = ofTerm g := by
  induction d generalizing B with
  | pure hA =>
    induction c with
    | pure hB => exact pure_positive_coherence f g hf hg hA hB h
    | @conj B D c d ih ih' =>
      apply Reduced.conj_ext
      · apply ih (.comp f (.fst B D)) (.comp g (.fst B D))
          (.comp hf (.fst B D)) (.comp hg (.fst B D))
        change Relations.comp f.relation Relations.fstRel = Relations.comp g.relation Relations.fstRel
        rw [h]
      · apply ih' (.comp f (.snd B D)) (.comp g (.snd B D))
          (.comp hf (.snd B D)) (.comp hg (.snd B D))
        change Relations.comp f.relation Relations.sndRel = Relations.comp g.relation Relations.sndRel
        rw [h]
  | @disj A D d e ih ih' =>
    apply Reduced.disj_ext
    · apply ih c (.comp (.inl A D) f) (.comp (.inl A D) g)
        (.comp (.inl A D) hf) (.comp (.inl A D) hg)
      change Relations.comp (Relations.graph Sum.inl) f.relation =
        Relations.comp (Relations.graph Sum.inl) g.relation
      rw [h]
    · apply ih' c (.comp (.inr A D) f) (.comp (.inr A D) g)
        (.comp (.inr A D) hf) (.comp (.inr A D) hg)
      change Relations.comp (Relations.graph Sum.inr) f.relation =
        Relations.comp (Relations.graph Sum.inr) g.relation
      rw [h]

end DosenPetric.Reduced.Gentzen
