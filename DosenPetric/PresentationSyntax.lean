module

public import DosenPetric.Formula

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.Presentation

universe u

/-- The two covariant binary operations of the published arrow grammar. -/
inductive Op where
  | conj
  | disj

namespace Op

abbrev formula {P : Type u} : Op → Formula P → Formula P → Formula P
  | .conj => Formula.conj
  | .disj => Formula.disj

abbrev unit {P : Type u} : Op → Formula P
  | .conj => .top
  | .disj => .bot

end Op

/-- The primitive grammar C(B), September 2007, pp.310,312,316.
`comp f g` denotes the book's g ∘ f. `swap .disj A B` denotes its c_(B,A).
Negation on arrows, pairing, copairing, and dR are derived operations. -/
inductive Term (P : Type u) : Formula P → Formula P → Type u where
  | id (A) : Term P A A
  | comp {A B C} : Term P A B → Term P B C → Term P A C
  | tensor (o : Op) {A B C D} : Term P A C → Term P B D →
      Term P (o.formula A B) (o.formula C D)
  | assocR (o : Op) (A B C) : Term P (o.formula A (o.formula B C)) (o.formula (o.formula A B) C)
  | assocL (o : Op) (A B C) : Term P (o.formula (o.formula A B) C) (o.formula A (o.formula B C))
  | swap (o : Op) (A B) : Term P (o.formula A B) (o.formula B A)
  | diag (A) : Term P A (.conj A A)
  | codiag (A) : Term P (.disj A A) A
  | fst (A B) : Term P (.conj A B) A
  | snd (A B) : Term P (.conj A B) B
  | inl (A B) : Term P A (.disj A B)
  | inr (A B) : Term P B (.disj A B)
  | rightOut (o : Op) (A) : Term P (o.formula A o.unit) A
  | rightIn (o : Op) (A) : Term P A (o.formula A o.unit)
  | leftOut (o : Op) (A) : Term P (o.formula o.unit A) A
  | leftIn (o : Op) (A) : Term P A (o.formula o.unit A)
  | mix (A B) : Term P (.conj A B) (.disj A B)
  | dist (A B C) : Term P (.conj A (.disj B C)) (.disj (.conj A B) C)
  | zero (A) : Term P A A
  | dnOut (A) : Term P (.neg (.neg A)) A
  | dnIn (A) : Term P A (.neg (.neg A))
  | dmConjOut (A B) : Term P (.neg (.conj A B)) (.disj (.neg A) (.neg B))
  | dmConjIn (A B) : Term P (.disj (.neg A) (.neg B)) (.neg (.conj A B))
  | dmDisjOut (A B) : Term P (.neg (.disj A B)) (.conj (.neg A) (.neg B))
  | dmDisjIn (A B) : Term P (.conj (.neg A) (.neg B)) (.neg (.disj A B))
  | negTopOut : Term P (.neg .top) .bot
  | negTopIn : Term P .bot (.neg .top)
  | negBotOut : Term P (.neg .bot) .top
  | negBotIn : Term P .top (.neg .bot)
  | excludedMiddle (A) : Term P .top (.disj (.neg A) A)
  | contradiction (A) : Term P (.conj A (.neg A)) .bot

namespace Term

variable {P : Type u}

/-- (⟨ , ⟩), p.187. -/
def pair {X A B : Formula P} (f : Term P X A) (g : Term P X B) : Term P X (.conj A B) :=
  .comp (.diag X) (.tensor .conj f g)

/-- The dual copairing definition, p.198. -/
def copair {A B X : Formula P} (f : Term P A X) (g : Term P B X) : Term P (.disj A B) X :=
  .comp (.tensor .disj f g) (.codiag X)

/-- The terminal-arrow definition, p.191. -/
def toTop (A : Formula P) : Term P A .top := .comp (.rightIn .conj A) (.snd A .top)

/-- The initial-arrow definition, p.207. -/
def fromBot (A : Formula P) : Term P .bot A := .comp (.inr A .bot) (.rightOut .disj A)

/-- (dR c), p.145, with the disjunctive symmetry indices translated. -/
def distRight (A B C : Formula P) : Term P (.conj (.disj A B) C) (.disj A (.conj B C)) :=
  .comp (.swap .conj (.disj A B) C)
    (.comp (.tensor .conj (.id C) (.swap .disj A B))
      (.comp (.dist C B A)
        (.comp (.tensor .disj (.swap .conj C B) (.id A)) (.swap .disj (.conj B C) A))))

/-- The medial arrow used in (b c w), p.186. -/
def medial (o : Op) (A B C D : Formula P) :
    Term P (o.formula (o.formula A B) (o.formula C D)) (o.formula (o.formula A C) (o.formula B D)) :=
  .comp (.assocL o A B (o.formula C D))
    (.comp (.tensor o (.id A)
      (.comp (.assocR o B C D) (.comp (.tensor o (.swap o B C) (.id D)) (.assocL o C B D))))
      (.assocR o A C (o.formula B D)))

/-- The source-defined zero endomorphism (0ηε), p.317, before proving its equation. -/
def zeroConstruction (A : Formula P) : Term P A A :=
  .comp (.rightIn .conj A)
    (.comp (.tensor .conj (.id A) (.excludedMiddle A))
      (.comp (.dist A (.neg A) A)
        (.comp (.tensor .disj (.contradiction A) (.id A)) (.leftOut .disj A))))

end Term

end DosenPetric.Presentation
