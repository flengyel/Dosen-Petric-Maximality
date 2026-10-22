module

public import DosenPetric.PresentationSignedLabels

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.Reduced

universe u

/-- The two covariant binary operations of the published arrow grammar. -/
inductive Op where
  | conj
  | disj

namespace Op

abbrev formula {P : Type u} : Op → NormalForm P → NormalForm P → NormalForm P
  | .conj => NormalForm.conj
  | .disj => NormalForm.disj

abbrev unit {P : Type u} : Op → NormalForm P
  | .conj => .top
  | .disj => .bot

def full : Op → Presentation.Op
  | .conj => .conj
  | .disj => .disj

end Op

/-- The reduced grammar C(C), printed p.318. Only atomic eta/epsilon are primitive. -/
inductive Term (P : Type u) : NormalForm P → NormalForm P → Type u where
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
  | eta (p : P) : Term P .top (.disj (.lit (.neg p)) (.lit (.pos p)))
  | epsilon (p : P) : Term P (.conj (.lit (.pos p)) (.lit (.neg p))) .bot

namespace Term

variable {P : Type u}

/-- (⟨ , ⟩), p.187. -/
def pair {X A B : NormalForm P} (f : Term P X A) (g : Term P X B) : Term P X (.conj A B) :=
  .comp (.diag X) (.tensor .conj f g)

/-- The dual copairing definition, p.198. -/
def copair {A B X : NormalForm P} (f : Term P A X) (g : Term P B X) : Term P (.disj A B) X :=
  .comp (.tensor .disj f g) (.codiag X)

/-- The terminal-arrow definition, p.191. -/
def toTop (A : NormalForm P) : Term P A .top := .comp (.rightIn .conj A) (.snd A .top)

/-- The initial-arrow definition, p.207. -/
def fromBot (A : NormalForm P) : Term P .bot A := .comp (.inr A .bot) (.rightOut .disj A)

/-- (dR c), p.145, with the disjunctive symmetry indices translated. -/
def distRight (A B C : NormalForm P) : Term P (.conj (.disj A B) C) (.disj A (.conj B C)) :=
  .comp (.swap .conj (.disj A B) C)
    (.comp (.tensor .conj (.id C) (.swap .disj A B))
      (.comp (.dist C B A)
        (.comp (.tensor .disj (.swap .conj C B) (.id A)) (.swap .disj (.conj B C) A))))

/-- The medial arrow used in (b c w), p.186. -/
def medial (o : Op) (A B C D : NormalForm P) :
    Term P (o.formula (o.formula A B) (o.formula C D)) (o.formula (o.formula A C) (o.formula B D)) :=
  .comp (.assocL o A B (o.formula C D))
    (.comp (.tensor o (.id A)
      (.comp (.assocR o B C D) (.comp (.tensor o (.swap o B C) (.id D)) (.assocL o C B D))))
      (.assocR o A C (o.formula B D)))

end Term

end DosenPetric.Reduced
