module

public import DosenPetric.SemanticSignature

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.PresentationSemantics
universe u v w
variable {X : Type u}

/-- Interpret every object constructor from a variable valuation. -/
def formula (O : Objects X) {P : Type w} (α : P → X) : Formula P → X
  | .var p => α p
  | .top => O.top
  | .bot => O.bot
  | .conj A B => O.conj (formula O α A) (formula O α B)
  | .disj A B => O.disj (formula O α A) (formula O α B)
  | .neg A => O.neg (formula O α A)

namespace Primitives
variable {C : Category.{u,v} X} {O : Objects X}

/-- Evaluation follows the complete primitive source grammar. -/
def evaluate (S : Primitives C O) {P : Type w} (α : P → X) :
    {A B : Formula P} → Presentation.Term P A B → C.Hom (formula O α A) (formula O α B)
  | _,_,.id A => C.id (formula O α A)
  | _,_,.comp f g => C.comp (S.evaluate α f) (S.evaluate α g)
  | _,_,.tensor .conj f g => S.tensor .conj (S.evaluate α f) (S.evaluate α g)
  | _,_,.tensor .disj f g => S.tensor .disj (S.evaluate α f) (S.evaluate α g)
  | _,_,.assocR .conj A B D => S.assocR .conj (formula O α A) (formula O α B) (formula O α D)
  | _,_,.assocR .disj A B D => S.assocR .disj (formula O α A) (formula O α B) (formula O α D)
  | _,_,.assocL .conj A B D => S.assocL .conj (formula O α A) (formula O α B) (formula O α D)
  | _,_,.assocL .disj A B D => S.assocL .disj (formula O α A) (formula O α B) (formula O α D)
  | _,_,.swap .conj A B => S.swap .conj (formula O α A) (formula O α B)
  | _,_,.swap .disj A B => S.swap .disj (formula O α A) (formula O α B)
  | _,_,.diag A => S.diag (formula O α A)
  | _,_,.codiag A => S.codiag (formula O α A)
  | _,_,.fst A B => S.fst (formula O α A) (formula O α B)
  | _,_,.snd A B => S.snd (formula O α A) (formula O α B)
  | _,_,.inl A B => S.inl (formula O α A) (formula O α B)
  | _,_,.inr A B => S.inr (formula O α A) (formula O α B)
  | _,_,.rightOut .conj A => S.rightOut .conj (formula O α A)
  | _,_,.rightOut .disj A => S.rightOut .disj (formula O α A)
  | _,_,.rightIn .conj A => S.rightIn .conj (formula O α A)
  | _,_,.rightIn .disj A => S.rightIn .disj (formula O α A)
  | _,_,.leftOut .conj A => S.leftOut .conj (formula O α A)
  | _,_,.leftOut .disj A => S.leftOut .disj (formula O α A)
  | _,_,.leftIn .conj A => S.leftIn .conj (formula O α A)
  | _,_,.leftIn .disj A => S.leftIn .disj (formula O α A)
  | _,_,.mix A B => S.mix (formula O α A) (formula O α B)
  | _,_,.dist A B D => S.dist (formula O α A) (formula O α B) (formula O α D)
  | _,_,.zero A => S.zero (formula O α A)
  | _,_,.dnOut A => S.dnOut (formula O α A)
  | _,_,.dnIn A => S.dnIn (formula O α A)
  | _,_,.dmConjOut A B => S.dmConjOut (formula O α A) (formula O α B)
  | _,_,.dmConjIn A B => S.dmConjIn (formula O α A) (formula O α B)
  | _,_,.dmDisjOut A B => S.dmDisjOut (formula O α A) (formula O α B)
  | _,_,.dmDisjIn A B => S.dmDisjIn (formula O α A) (formula O α B)
  | _,_,.negTopOut => S.negTopOut
  | _,_,.negTopIn => S.negTopIn
  | _,_,.negBotOut => S.negBotOut
  | _,_,.negBotIn => S.negBotIn
  | _,_,.excludedMiddle A => S.excludedMiddle (formula O α A)
  | _,_,.contradiction A => S.contradiction (formula O α A)

/-- A model of the full primitive presentation satisfies each published
schema at every valuation. Preservation of generated equality is proved next. -/
def SatisfiesTheory (P : Type w) (S : Primitives C O) : Prop :=
  ∀ (α : P → X) {A B : Formula P} {f g : Presentation.Term P A B},
    Presentation.Equation f g → S.evaluate α f = S.evaluate α g

end Primitives
end DosenPetric.PresentationSemantics
