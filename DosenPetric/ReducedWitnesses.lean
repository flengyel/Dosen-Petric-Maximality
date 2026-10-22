module

public import DosenPetric.ReducedCategory

@[expose] public section

set_option autoImplicit false

namespace DosenPetric

universe u

theorem congrArgTwo {X Y Z : Type u} (f : X → Y → Z) {x x' : X} {y y' : Y}
    (hx : x = x') (hy : y = y') : f x y = f x' y' := by
  cases hx; cases hy; rfl

namespace NormalForm

variable {P : Type u}

/-- De Morgan duality on signed normal forms, without an operation on arrows. -/
def dual : NormalForm P → NormalForm P
  | .lit l => .lit l.flip
  | .top => .bot
  | .bot => .top
  | .conj A B => .disj A.dual B.dual
  | .disj A B => .conj A.dual B.dual

theorem dual_dual (A : NormalForm P) : A.dual.dual = A := by
  induction A with
  | lit l => exact congrArg NormalForm.lit (Literal.flip_flip l)
  | top => rfl
  | bot => rfl
  | conj A B ih ih' => exact congrArgTwo NormalForm.conj ih ih'
  | disj A B ih ih' => exact congrArgTwo NormalForm.disj ih ih'

end NormalForm

namespace Presentation.NegationNormalization

variable {P : Type u}

theorem form_true (A : Formula P) : form A true = (form A false).dual := by
  induction A with
  | var p => rfl
  | top => rfl
  | bot => rfl
  | conj A B ih ih' => exact congrArgTwo NormalForm.disj ih ih'
  | disj A B ih ih' => exact congrArgTwo NormalForm.conj ih ih'
  | neg A ih =>
    change form A false = (form A true).dual
    rw [ih, NormalForm.dual_dual]

theorem normal_formula (A : NormalForm P) : normal A.formula = A := by
  induction A with
  | lit l => cases l <;> rfl
  | top => rfl
  | bot => rfl
  | conj A B ih ih' => exact congrArgTwo NormalForm.conj ih ih'
  | disj A B ih ih' => exact congrArgTwo NormalForm.disj ih ih'

theorem normal_neg_formula (A : NormalForm P) : normal (.neg A.formula) = A.dual := by
  change form A.formula true = A.dual
  rw [form_true]
  exact congrArg NormalForm.dual (normal_formula A)

end Presentation.NegationNormalization

namespace Presentation

variable {P : Type u}

theorem zero_top : zero (Formula.top : Formula P) = id .top :=
  ((operations P).toTop_unique (zero .top)).trans ((operations P).toTop_unique (id .top)).symm

/-- Parallel arrows from top are equal by the zero law and terminality. -/
theorem fromTop_unique {A : Formula P} (f g : Hom .top A) : f = g := by
  have hf := Laws.zero_law f g
  have hg := Laws.zero_law g g
  rw [zero_top, Laws.id_comp] at hf hg
  exact hf.trans hg.symm

end Presentation

namespace Reduced.Term

variable {P : Type u}

/-- The mixed e'-disjunction type used by the eta equations on printed p.317. -/
def mixedDisj (A B C D : NormalForm P) :
    Term P (.conj (.disj A B) (.disj C D)) (.disj (.conj A C) (.disj B D)) :=
  .comp (.dist (.disj A B) C D)
    (.comp (.tensor .disj
      (.comp (.swap .conj (.disj A B) C)
        (.comp (.dist C A B) (.tensor .disj (.swap .conj C A) (.id B)))) (.id D))
      (.assocL .disj (.conj A C) B D))

/-- The mixed e'-conjunction type used by the epsilon equations on p.317. -/
def mixedConj (A B C D : NormalForm P) :
    Term P (.conj (.conj A B) (.disj C D)) (.disj (.conj A C) (.conj B D)) :=
  .comp (.tensor .conj (.swap .conj A B) (.id (.disj C D)))
    (.comp (.assocL .conj B A (.disj C D))
      (.comp (.tensor .conj (.id B) (.dist A C D))
        (.comp (.swap .conj B (.disj (.conj A C) D))
          (.comp (.distRight (.conj A C) D B)
            (.tensor .disj (.id (.conj A C)) (.swap .conj D B))))))

/-- Compound eta terms use only atomic eta, structural arrows and the two tensors. -/
def etaNF : (A : NormalForm P) → Term P .top (.disj A.dual A)
  | .lit (.pos p) => .eta p
  | .lit (.neg p) => .comp (.eta p) (.swap .disj (.lit (.neg p)) (.lit (.pos p)))
  | .top => .leftIn .disj .top
  | .bot => .rightIn .disj .top
  | .conj A B =>
    .comp (.rightIn .conj .top)
      (.comp (.tensor .conj (etaNF A) (etaNF B))
        (.comp (.tensor .conj (.swap .disj A.dual A) (.swap .disj B.dual B))
          (.comp (mixedDisj A A.dual B B.dual)
            (.swap .disj (.conj A B) (.disj A.dual B.dual)))))
  | .disj A B =>
    .comp (.rightIn .conj .top)
      (.comp (.tensor .conj (etaNF A) (etaNF B)) (mixedDisj A.dual A B.dual B))

def epsilonNF : (A : NormalForm P) → Term P (.conj A A.dual) .bot
  | .lit (.pos p) => .epsilon p
  | .lit (.neg p) => .comp (.swap .conj (.lit (.neg p)) (.lit (.pos p))) (.epsilon p)
  | .top => .leftOut .conj .bot
  | .bot => .rightOut .conj .bot
  | .conj A B =>
    .comp (mixedConj A B A.dual B.dual)
      (.comp (.tensor .disj (epsilonNF A) (epsilonNF B)) (.rightOut .disj .bot))
  | .disj A B =>
    .comp (.swap .conj (.disj A B) (.conj A.dual B.dual))
      (.comp (mixedConj A.dual B.dual A B)
        (.comp (.tensor .disj (.swap .conj A.dual A) (.swap .conj B.dual B))
          (.comp (.tensor .disj (epsilonNF A) (epsilonNF B)) (.rightOut .disj .bot))))

end Reduced.Term
end DosenPetric
