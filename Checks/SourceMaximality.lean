module
import DosenPetric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric
namespace SourceMaximalityChecks
example (P : Type u) : Functor (Presentation.category P) (Reduced.category P) := Reduced.reductionFunctor P
example (P : Type u) : Functor (Reduced.category P) (Presentation.category P) := Reduced.inclusionFunctor P
example (P : Type u) : NaturalIsomorphism (Functor.identity (Presentation.category P))
    ((Reduced.reductionFunctor P).comp (Reduced.inclusionFunctor P)) := Reduced.normalizationNaturalIso P
example (P : Type u) : Functor (opposite (Presentation.category P)) (Presentation.category P) := Presentation.negationFunctor P
example (P : Type u) : NaturalIsomorphism (Presentation.doubleNegationFunctor P)
    (Functor.identity (Presentation.category P)) := Presentation.doubleNegationNaturalIso P
example {P : Type u} {A B : Formula P} (f : Presentation.Term P A B) :
    Presentation.Term P (.neg B) (.neg A) := f.negate
example {P : Type u} (Q : Presentation.ProofCongruence P) (h : Q.Closed)
    {A B : Formula P} (f g : Presentation.Hom A B) (hne : f ≠ g) (hf : Q.Rel f g) : Q.Total :=
  Presentation.maximality Q h f g hne hf
example {P : Type u} (Q : Presentation.ProofCongruence P) (h : Q.Closed) :
    (∀ {A B} (f g : Presentation.Hom A B), Q.Rel f g ↔ f = g) ∨ Q.Total :=
  Presentation.congruence_dichotomy Q h
example {P : Type u} (Q : Presentation.RawProofCongruence P) (h : Q.Closed)
    {A B : Formula P} (f g : Presentation.Term P A B) (hne : ¬ Presentation.Derives f g) (hf : Q.Rel f g) :
    ∀ {C D} (k l : Presentation.Term P C D), Q.Rel k l := Presentation.raw_maximality Q h f g hne hf
example : Presentation.Hom (.neg (.conj (.var 0) (.var 0) : Formula Nat)) (.neg (.var 0)) :=
  Presentation.negate (Presentation.diag (.var 0))
example : Presentation.Hom (.neg (.top : Formula Empty)) (.neg .top) := Presentation.negate (Presentation.id .top)
example : ¬ Nonempty ((Presentation.category Empty).Hom .top .bot) := Presentation.empty_hom Empty
example : (Presentation.operations Nat).fst (.var 0) (.var 0) ≠
    (Presentation.operations Nat).snd (.var 0) (.var 0) := Presentation.nonthin 0

section
open DosenPetric.Reduced
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
example {P : Type u} {A B : Formula P} {f g : Presentation.Hom A B}
    (h : reduceHom f = reduceHom g) : f = g := reduceHom_injective h
end

section
open DosenPetric.Reduced
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
example {P : Type u} {A B : NormalForm P} (f : Hom A B) :
    castHom (Presentation.NegationNormalization.normal_formula A)
      (Presentation.NegationNormalization.normal_formula B) (reduceHom (inclusion f)) = f := reduction_inclusion f
end

section
open DosenPetric.Reduced
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
example {P : Type u} {A B : Formula P} (f : Presentation.Hom A B) : recoverHom (reduceHom f) = f := recover_reduceHom f
end

section
open DosenPetric.Reduced
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
example {P : Type u} {A B : Formula P} (f : Hom (normal A) (normal B)) :
    reduceHom (recoverHom f) = f := reduce_recoverHom f
end

section
open DosenPetric.Reduced
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
example {P : Type u} {A B : NormalForm P} (f : Hom A B)
    (x : A.formula.Occ) (y : B.formula.Occ) :
    occurrenceMap (dualHom f) (toDual B y) (toDual A x) ↔ occurrenceMap f x y := dualHom_relation f x y
end

section
open DosenPetric.Reduced
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
example {P : Type u} {A B : NormalForm P} (f : Hom A B) :
    castHom (NormalForm.dual_dual A) (NormalForm.dual_dual B) (dualHom (dualHom f)) = f := dualHom_involutive f
end

section
open DosenPetric.Reduced
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
example {P : Type u} {A B : Formula P} (f : Presentation.Hom A B) :
    negReduceHom (Presentation.negate f) = reduceHom f := negReduceHom_twice f
end

section
open DosenPetric.Presentation
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
example {P : Type u} {A B : Formula P} (f : Hom A B) :
    comp (negate (negate f)) (dnOut B) = comp (dnOut A) f := dnOut_natural f
end

section
open DosenPetric.Presentation
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
example {P : Type u} {A B : Formula P} (f : Hom A B) :
    comp f (dnIn B) = comp (dnIn A) (negate (negate f)) := dnIn_natural f
end

section
open DosenPetric.Presentation
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
example {P : Type u} {A B C D : Formula P} (f : Hom A C) (g : Hom B D) :
    comp (negate (tensor .conj f g)) (dmConjOut A B) =
      comp (dmConjOut C D) (tensor .disj (negate f) (negate g)) := dmConjOut_natural f g
end

section
open DosenPetric.Presentation
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
example {P : Type u} {A B C D : Formula P} (f : Hom A C) (g : Hom B D) :
    comp (tensor .disj (negate f) (negate g)) (dmConjIn A B) =
      comp (dmConjIn C D) (negate (tensor .conj f g)) := dmConjIn_natural f g
end

section
open DosenPetric.Presentation
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
example {P : Type u} {A B C D : Formula P} (f : Hom A C) (g : Hom B D) :
    comp (negate (tensor .disj f g)) (dmDisjOut A B) =
      comp (dmDisjOut C D) (tensor .conj (negate f) (negate g)) := dmDisjOut_natural f g
end

section
open DosenPetric.Presentation
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
example {P : Type u} {A B C D : Formula P} (f : Hom A C) (g : Hom B D) :
    comp (tensor .conj (negate f) (negate g)) (dmDisjIn A B) =
      comp (dmDisjIn C D) (negate (tensor .disj f g)) := dmDisjIn_natural f g
end

section
open DosenPetric.Presentation.NegationNormalization
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
open DosenPetric.Presentation
example {P : Type u} (A : Formula P) (s : Bool) :
    ofTerm (forwardTerm A s) = (comparison A s).forward := forwardTerm_denotes A s
end

section
open DosenPetric.Presentation.NegationNormalization
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
open DosenPetric.Presentation
example {P : Type u} (A : Formula P) (s : Bool) :
    ofTerm (backwardTerm A s) = (comparison A s).backward := backwardTerm_denotes A s
end

section
open DosenPetric.Presentation
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
example {P : Type u} {A B : Formula P} (f : Term P A B) :
    ofTerm f.negate = negate (ofTerm f) := negateTerm_denotes f
end

section
open DosenPetric.Presentation
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
example {P : Type u} {A B : Formula P} {f g : Term P A B} (h : Derives f g) :
    Derives f.negate g.negate := negate_derives h
end

section
open DosenPetric.Presentation.NegationNormalization
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
open DosenPetric.Presentation
example {P : Type u} (A : Formula P) (x : A.Occ) :
    castOcc (form_true A) (toOcc (.neg A) x) = NormalForm.toDual (normal A) (toOcc A x) := toOcc_neg A x
end

section
open DosenPetric.Presentation
open DosenPetric.Presentation.NegationNormalization (normal)
open DosenPetric.NormalForm (toDual castOcc)
example {P : Type u} {A B : Formula P} (f : Hom A B) (x : A.Occ) (y : B.Occ) :
    occurrenceMap (negate f) y x ↔ occurrenceMap f x y := occurrence_negate f x y
end

example {P : Type u} (Q : Presentation.RawProofCongruence P) {A B : Formula P}
    (f g : Presentation.Term P A B) : Q.toQuotient.toRaw.Rel f g ↔ Q.Rel f g := Q.quotient_raw_rel f g
example {P : Type u} (Q : Presentation.ProofCongruence P) {A B : Formula P}
    (f g : Presentation.Hom A B) : Q.toRaw.toQuotient.Rel f g ↔ Q.Rel f g := Q.raw_quotient_rel f g
example {P : Type u} (Q : Presentation.RawProofCongruence P) (h : Q.Closed) : Q.toQuotient.Closed := Q.toQuotient_closed h
example {P : Type u} (Q : Presentation.ProofCongruence P) (h : Q.Closed) : Q.toRaw.Closed := Q.toRaw_closed h
example {P : Type u} (Q : Presentation.ProofCongruence P) (h : Q.Closed) :
    (Presentation.substitution P).Closed Q.fragment := Q.fragment_closed h
end SourceMaximalityChecks

#print axioms DosenPetric.Reduced.reduceHom_injective

#print axioms DosenPetric.Reduced.reduction_inclusion

#print axioms DosenPetric.Reduced.recover_reduceHom

#print axioms DosenPetric.Reduced.reduce_recoverHom

#print axioms DosenPetric.Reduced.dualHom_relation

#print axioms DosenPetric.Reduced.dualHom_involutive

#print axioms DosenPetric.Reduced.negReduceHom_twice

#print axioms DosenPetric.Presentation.dnOut_natural

#print axioms DosenPetric.Presentation.dnIn_natural

#print axioms DosenPetric.Presentation.dmConjOut_natural

#print axioms DosenPetric.Presentation.dmConjIn_natural

#print axioms DosenPetric.Presentation.dmDisjOut_natural

#print axioms DosenPetric.Presentation.dmDisjIn_natural

#print axioms DosenPetric.Presentation.NegationNormalization.forwardTerm_denotes

#print axioms DosenPetric.Presentation.NegationNormalization.backwardTerm_denotes

#print axioms DosenPetric.Presentation.negateTerm_denotes

#print axioms DosenPetric.Presentation.negate_derives

#print axioms DosenPetric.Presentation.NegationNormalization.toOcc_neg

#print axioms DosenPetric.Presentation.occurrence_negate

#print axioms DosenPetric.Presentation.maximality

#print axioms DosenPetric.Presentation.congruence_dichotomy

#print axioms DosenPetric.Presentation.raw_maximality

#print axioms DosenPetric.Presentation.RawProofCongruence.toQuotient

#print axioms DosenPetric.Presentation.ProofCongruence.toRaw

#print axioms DosenPetric.Presentation.ProofCongruence.raw_quotient_rel

#print axioms DosenPetric.Presentation.RawProofCongruence.quotient_raw_rel
