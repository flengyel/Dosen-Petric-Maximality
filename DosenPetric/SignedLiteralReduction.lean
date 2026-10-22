module

public import DosenPetric.ReductionTransport

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.Reduced

universe u

variable {P : Type u}

open Presentation.NegationNormalization (normal)

abbrev includeTerm {A B : NormalForm P} (t : Term P A B) : Presentation.Hom A.formula B.formula :=
  Presentation.ofTerm t.toFull

def Term.cast {A B A' B' : NormalForm P} (ha : A = A') (hb : B = B')
    (t : Term P A B) : Term P A' B' := ha ▸ hb ▸ t

theorem includeTerm_cast {A B A' B' : NormalForm P} (ha : A = A') (hb : B = B')
    (t : Term P A B) : includeTerm (t.cast ha hb) =
      Presentation.castHom (congrArg NormalForm.formula ha) (congrArg NormalForm.formula hb)
        (includeTerm t) := by
  cases ha; cases hb; rfl

def redEta (A : Formula P) : Term P .top (normal (.disj (.neg A) A)) :=
  (Term.etaNF (normal A)).cast rfl
    (congrArgTwo NormalForm.disj (Presentation.NegationNormalization.form_true A).symm rfl)

def redEpsilon (A : Formula P) : Term P (normal (.conj A (.neg A))) .bot :=
  (Term.epsilonNF (normal A)).cast
    (congrArgTwo NormalForm.conj rfl (Presentation.NegationNormalization.form_true A).symm) rfl

/-- Normalized representatives in C(C), chosen on full raw terms, not quotient arrows. -/
def red : {A B : Formula P} → Presentation.Term P A B → Term P (normal A) (normal B)
  | _, _, .id A => .id (normal A)
  | _, _, .comp f g => .comp (red f) (red g)
  | _, _, .tensor .conj f g => .tensor .conj (red f) (red g)
  | _, _, .tensor .disj f g => .tensor .disj (red f) (red g)
  | _, _, .assocR .conj A B C => .assocR .conj (normal A) (normal B) (normal C)
  | _, _, .assocR .disj A B C => .assocR .disj (normal A) (normal B) (normal C)
  | _, _, .assocL .conj A B C => .assocL .conj (normal A) (normal B) (normal C)
  | _, _, .assocL .disj A B C => .assocL .disj (normal A) (normal B) (normal C)
  | _, _, .swap .conj A B => .swap .conj (normal A) (normal B)
  | _, _, .swap .disj A B => .swap .disj (normal A) (normal B)
  | _, _, .diag A => .diag (normal A)
  | _, _, .codiag A => .codiag (normal A)
  | _, _, .fst A B => .fst (normal A) (normal B)
  | _, _, .snd A B => .snd (normal A) (normal B)
  | _, _, .inl A B => .inl (normal A) (normal B)
  | _, _, .inr A B => .inr (normal A) (normal B)
  | _, _, .rightOut .conj A => .rightOut .conj (normal A)
  | _, _, .rightOut .disj A => .rightOut .disj (normal A)
  | _, _, .rightIn .conj A => .rightIn .conj (normal A)
  | _, _, .rightIn .disj A => .rightIn .disj (normal A)
  | _, _, .leftOut .conj A => .leftOut .conj (normal A)
  | _, _, .leftOut .disj A => .leftOut .disj (normal A)
  | _, _, .leftIn .conj A => .leftIn .conj (normal A)
  | _, _, .leftIn .disj A => .leftIn .disj (normal A)
  | _, _, .mix A B => .mix (normal A) (normal B)
  | _, _, .dist A B C => .dist (normal A) (normal B) (normal C)
  | _, _, .zero A => .zero (normal A)
  | _, _, .dnOut A => .id (normal A)
  | _, _, .dnIn A => .id (normal A)
  | _, _, .dmConjOut A B => .id (.disj (normal (.neg A)) (normal (.neg B)))
  | _, _, .dmConjIn A B => .id (.disj (normal (.neg A)) (normal (.neg B)))
  | _, _, .dmDisjOut A B => .id (.conj (normal (.neg A)) (normal (.neg B)))
  | _, _, .dmDisjIn A B => .id (.conj (normal (.neg A)) (normal (.neg B)))
  | _, _, .negTopOut => .id .bot
  | _, _, .negTopIn => .id .bot
  | _, _, .negBotOut => .id .top
  | _, _, .negBotIn => .id .top
  | _, _, .excludedMiddle A => redEta A
  | _, _, .contradiction A => redEpsilon A

namespace Compatibility

open Presentation
open Presentation.NegationNormalization

def negForward (A : NormalForm P) : Presentation.Hom (.neg A.formula) A.dual.formula :=
  Presentation.castHom rfl (congrArg NormalForm.formula (normal_neg_formula A))
    (forward (.neg A.formula))

def negBackward (A : NormalForm P) : Presentation.Hom A.dual.formula (.neg A.formula) :=
  Presentation.castHom (congrArg NormalForm.formula (normal_neg_formula A)) rfl
    (backward (.neg A.formula))

theorem etaNF (A : NormalForm P) : includeTerm (Term.etaNF A) =
    Presentation.comp (excludedMiddle A.formula)
      (Presentation.tensor .disj (negForward A) (Presentation.id A.formula)) :=
  fromTop_unique _ _

theorem epsilonNF (A : NormalForm P) : includeTerm (Term.epsilonNF A) =
    Presentation.comp (Presentation.tensor .conj (Presentation.id A.formula) (negBackward A))
      (contradiction A.formula) := toBot_unique _ _

theorem eta (A : Formula P) : includeTerm (redEta A) =
    (normalization P).transport (excludedMiddle A) := fromTop_unique _ _

theorem epsilon (A : Formula P) : includeTerm (redEpsilon A) =
    (normalization P).transport (contradiction A) := toBot_unique _ _

end Compatibility

/-- Inclusion of every chosen representative equals the existing normalizer transport. -/
theorem red_sound {A B : Formula P} (t : Presentation.Term P A B) :
    includeTerm (red t) = (Presentation.normalization P).transport (Presentation.ofTerm t) := by
  induction t with
  | id A => exact (Presentation.NegationNormalization.transport_id A).symm
  | comp f g ih ih' =>
    change Presentation.comp (includeTerm (red f)) (includeTerm (red g)) =
      (Presentation.normalization P).transport (Presentation.comp (Presentation.ofTerm f) (Presentation.ofTerm g))
    rw [ih, ih', Presentation.NegationNormalization.transport_comp]
    rfl
  | tensor o f g ih ih' =>
    cases o
    · change Presentation.tensor .conj (includeTerm (red f)) (includeTerm (red g)) =
        (Presentation.normalization P).transport (Presentation.tensor .conj (Presentation.ofTerm f) (Presentation.ofTerm g))
      rw [ih, ih', Presentation.NegationNormalization.transport_tensor_conj]
      rfl
    · change Presentation.tensor .disj (includeTerm (red f)) (includeTerm (red g)) =
        (Presentation.normalization P).transport (Presentation.tensor .disj (Presentation.ofTerm f) (Presentation.ofTerm g))
      rw [ih, ih', Presentation.NegationNormalization.transport_tensor_disj]
      rfl
  | assocR o A B C =>
    cases o <;> symm <;>
      apply Presentation.NegationNormalization.transport_eq_of_square <;>
      exact Presentation.Laws.assocR_nat _ (Presentation.NegationNormalization.forward A) (Presentation.NegationNormalization.forward B) (Presentation.NegationNormalization.forward C)
  | assocL o A B C =>
    cases o <;> symm <;>
      apply Presentation.NegationNormalization.transport_eq_of_square <;>
      exact Presentation.Laws.assocL_nat _ (Presentation.NegationNormalization.forward A) (Presentation.NegationNormalization.forward B) (Presentation.NegationNormalization.forward C)
  | swap o A B =>
    cases o <;> symm <;>
      apply Presentation.NegationNormalization.transport_eq_of_square <;>
      exact Presentation.Laws.swap_nat _ (Presentation.NegationNormalization.forward A) (Presentation.NegationNormalization.forward B)
  | diag A =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    exact Presentation.Laws.diag_nat (Presentation.NegationNormalization.forward A)
  | codiag A =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    exact (Presentation.Laws.codiag_nat (Presentation.NegationNormalization.forward A)).symm
  | fst A B =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    exact Presentation.Laws.fst_nat (Presentation.NegationNormalization.forward A) (Presentation.NegationNormalization.forward B)
  | snd A B =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    exact Presentation.Laws.snd_nat (Presentation.NegationNormalization.forward A) (Presentation.NegationNormalization.forward B)
  | inl A B =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    exact Presentation.Laws.inl_nat (Presentation.NegationNormalization.forward A) (Presentation.NegationNormalization.forward B)
  | inr A B =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    exact Presentation.Laws.inr_nat (Presentation.NegationNormalization.forward A) (Presentation.NegationNormalization.forward B)
  | rightOut o A =>
    cases o <;> symm <;>
      apply Presentation.NegationNormalization.transport_eq_of_square <;>
      exact Presentation.Laws.rightOut_nat _ (Presentation.NegationNormalization.forward A)
  | rightIn o A =>
    cases o <;> symm <;>
      apply Presentation.NegationNormalization.transport_eq_of_square <;>
      exact Presentation.Laws.rightIn_nat _ (Presentation.NegationNormalization.forward A)
  | leftOut o A =>
    cases o <;> symm <;>
      apply Presentation.NegationNormalization.transport_eq_of_square <;>
      exact Presentation.Laws.leftOut_nat _ (Presentation.NegationNormalization.forward A)
  | leftIn o A =>
    cases o <;> symm <;>
      apply Presentation.NegationNormalization.transport_eq_of_square <;>
      exact Presentation.Laws.leftIn_nat _ (Presentation.NegationNormalization.forward A)
  | mix A B =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    exact Presentation.Laws.mix_nat (Presentation.NegationNormalization.forward A) (Presentation.NegationNormalization.forward B)
  | dist A B C =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    exact Presentation.Laws.dist_nat (Presentation.NegationNormalization.forward A) (Presentation.NegationNormalization.forward B) (Presentation.NegationNormalization.forward C)
  | zero A =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    exact Presentation.Laws.zero_law _ _
  | dnOut A =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    exact (Presentation.Laws.comp_id _).symm
  | dnIn A =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    change Presentation.comp (Presentation.dnIn A)
      (Presentation.comp (Presentation.dnOut A) (Presentation.NegationNormalization.forward A)) =
      Presentation.comp (Presentation.NegationNormalization.forward A) (Presentation.id _)
    rw [← Presentation.Laws.assoc, Presentation.Laws.dnOut_out, Presentation.Laws.id_comp, Presentation.Laws.comp_id]
  | dmConjOut A B =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    exact (Presentation.Laws.comp_id _).symm
  | dmConjIn A B =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    change Presentation.comp (Presentation.dmConjIn A B)
      (Presentation.comp (Presentation.dmConjOut A B)
        (Presentation.tensor .disj (Presentation.NegationNormalization.forward (.neg A))
          (Presentation.NegationNormalization.forward (.neg B)))) =
      Presentation.comp (Presentation.tensor .disj (Presentation.NegationNormalization.forward (.neg A))
        (Presentation.NegationNormalization.forward (.neg B))) (Presentation.id _)
    rw [← Presentation.Laws.assoc, Presentation.Laws.dmConjOut_out, Presentation.Laws.id_comp, Presentation.Laws.comp_id]
  | dmDisjOut A B =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    exact (Presentation.Laws.comp_id _).symm
  | dmDisjIn A B =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    change Presentation.comp (Presentation.dmDisjIn A B)
      (Presentation.comp (Presentation.dmDisjOut A B)
        (Presentation.tensor .conj (Presentation.NegationNormalization.forward (.neg A))
          (Presentation.NegationNormalization.forward (.neg B)))) =
      Presentation.comp (Presentation.tensor .conj (Presentation.NegationNormalization.forward (.neg A))
        (Presentation.NegationNormalization.forward (.neg B))) (Presentation.id _)
    rw [← Presentation.Laws.assoc, Presentation.Laws.dmDisjOut_out, Presentation.Laws.id_comp, Presentation.Laws.comp_id]
  | negTopOut =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    rfl
  | negTopIn =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    change Presentation.comp (Presentation.negTopIn (P := P)) Presentation.negTopOut =
      Presentation.comp (Presentation.id .bot) (Presentation.id .bot)
    rw [Presentation.Laws.negTopOut_out, Presentation.Laws.id_comp]
  | negBotOut =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    rfl
  | negBotIn =>
    symm
    apply Presentation.NegationNormalization.transport_eq_of_square
    change Presentation.comp (Presentation.negBotIn (P := P)) Presentation.negBotOut =
      Presentation.comp (Presentation.id .top) (Presentation.id .top)
    rw [Presentation.Laws.negBotOut_out, Presentation.Laws.id_comp]
  | excludedMiddle A => exact Compatibility.eta A
  | contradiction A => exact Compatibility.epsilon A

/-- Inclusion is surjective on hom-sets between signed normal forms.
This is existential representation, not descent of red to full quotient arrows. -/
theorem representation (A B : NormalForm P) (f : Presentation.Hom A.formula B.formula) :
    ∃ r : Hom A B, inclusion r = f := by
  induction f using Quotient.inductionOn with
  | h t =>
    refine ⟨ofTerm ((red t).cast (Presentation.NegationNormalization.normal_formula A)
      (Presentation.NegationNormalization.normal_formula B)), ?_⟩
    change includeTerm ((red t).cast _ _) = Presentation.ofTerm t
    rw [includeTerm_cast, red_sound]
    exact Presentation.NegationNormalization.transport_formula A B (Presentation.ofTerm t)

end DosenPetric.Reduced
