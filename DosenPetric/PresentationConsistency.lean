module

public import DosenPetric.PresentationZero

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.Presentation

universe u

variable {P : Type u}

/-- A Boolean truth valuation, including genuine propositional negation. -/
def Truth : Formula P → Prop
  | .var _ => True
  | .top => True
  | .bot => False
  | .conj A B => Truth A ∧ Truth B
  | .disj A B => Truth A ∨ Truth B
  | .neg A => ¬ Truth A

/-- This raw-term invariant suffices for empty hom-sets; no quotient faithfulness
or semantic definition of syntactic equality is used. -/
theorem Term.preserves_truth {A B : Formula P} (t : Term P A B) : Truth A → Truth B := by
  induction t with
  | id _ => exact _root_.id
  | comp _ _ hf hg => exact fun h => hg (hf h)
  | tensor o _ _ hf hg =>
    cases o
    · exact fun h => ⟨hf h.1, hg h.2⟩
    · exact fun h => h.elim (fun h => .inl (hf h)) (fun h => .inr (hg h))
  | assocR o _ _ _ =>
    cases o
    · exact fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩
    · intro h; rcases h with h | h | h
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr h
  | assocL o _ _ _ =>
    cases o
    · exact fun h => ⟨h.1.1, h.1.2, h.2⟩
    · intro h; rcases h with (h | h) | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
  | swap o _ _ =>
    cases o
    · exact fun h => ⟨h.2, h.1⟩
    · exact fun h => h.elim Or.inr Or.inl
  | diag _ => exact fun h => ⟨h, h⟩
  | codiag _ => exact fun h => h.elim _root_.id _root_.id
  | fst _ _ => exact And.left
  | snd _ _ => exact And.right
  | inl _ _ => exact Or.inl
  | inr _ _ => exact Or.inr
  | rightOut o _ =>
    cases o
    · exact And.left
    · exact fun h => h.elim _root_.id False.elim
  | rightIn o _ =>
    cases o
    · exact fun h => ⟨h, .intro⟩
    · exact Or.inl
  | leftOut o _ =>
    cases o
    · exact And.right
    · exact fun h => h.elim False.elim _root_.id
  | leftIn o _ =>
    cases o
    · exact fun h => ⟨.intro, h⟩
    · exact Or.inr
  | mix _ _ => exact fun h => Or.inl h.1
  | dist _ _ _ =>
    rintro ⟨ha, hb | hc⟩
    · exact .inl ⟨ha, hb⟩
    · exact .inr hc
  | zero _ => exact _root_.id
  | dnOut _ => exact fun h => Classical.byContradiction h
  | dnIn _ => exact fun h hn => hn h
  | dmConjOut A B =>
    intro h
    by_cases ha : Truth A
    · exact .inr (fun hb => h ⟨ha, hb⟩)
    · exact .inl ha
  | dmConjIn _ _ => exact fun h hab => h.elim (fun ha => ha hab.1) (fun hb => hb hab.2)
  | dmDisjOut _ _ => exact fun h => ⟨fun ha => h (.inl ha), fun hb => h (.inr hb)⟩
  | dmDisjIn _ _ => exact fun h hab => hab.elim h.1 h.2
  | negTopOut => exact fun h => h .intro
  | negTopIn => exact False.elim
  | negBotOut => exact fun _ => .intro
  | negBotIn => exact fun _ => False.elim
  | excludedMiddle A =>
    intro _
    by_cases h : Truth A
    · exact .inr h
    · exact .inl h
  | contradiction _ => exact fun h => h.2 h.1

/-- In particular this presentation has no arrow from top to bottom. -/
theorem empty_hom (P : Type u) : ¬ Nonempty (Hom (P := P) .top .bot) := by
  rintro ⟨f⟩
  induction f using Quotient.inductionOn with | h t =>
  exact t.preserves_truth True.intro

end DosenPetric.Presentation
