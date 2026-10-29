module

public import DosenPetric.PresentationShortQ

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation.ShortProof
universe u
variable {P : Type u}

/-- The source mixed conjunction comparison, now at arbitrary formula endpoints. -/
def sourceConjTerm (X Y A B : Formula P) :
    Term P (.conj (.conj X Y) (.disj A B)) (.disj (.conj X A) (.conj Y B)) :=
  .comp (.tensor .conj (.id (.conj X Y)) (.swap .disj A B))
    (.comp (.assocL .conj X Y (.disj B A))
      (.comp (.tensor .conj (.id X) (.dist Y B A))
        (.comp (.tensor .conj (.id X) (.swap .disj (.conj Y B) A))
          (.dist X A (.conj Y B)))))

def sectionTerm (X A B : Formula P) :
    Term P (.conj X (.disj A B)) (.disj (.conj X A) (.conj X B)) :=
  .comp (.tensor .conj (.diag X) (.id (.disj A B))) (sourceConjTerm X X A B)

/-- The manuscript's e_A is identity tensor the first injection. -/
def eTerm (A : Formula P) : Term P (.conj A A) (.conj A (.disj A .top)) :=
  .tensor .conj (.id A) (.inl A .top)

/-- The unused summand is killed by a zero with the explicit witness fst;diag. -/
def eInverseTerm (A : Formula P) : Term P (.conj A (.disj A .top)) (.conj A A) :=
  .comp (sectionTerm A A .top)
    (Term.copair (.id (.conj A A))
      (.comp (.zero (.conj A .top)) (.comp (.fst A .top) (.diag A))))

def e (A : Formula P) : Hom (.conj A A) (.conj A (.disj A .top)) := ofTerm (eTerm A)
def eInverse (A : Formula P) : Hom (.conj A (.disj A .top)) (.conj A A) := ofTerm (eInverseTerm A)

theorem e_definition (A : Formula P) : e A = tensor .conj (id A) (inl A .top) := rfl

attribute [local simp] Term.relation Relations.comp Relations.graph Relations.sumMap
  Relations.pair Relations.copair Relations.fstRel Relations.sndRel Relations.reassoc
  Relations.empty Occurrence.unassoc Occurrence.exchange Sum.exists Term.copair

theorem e_eInverse (A : Formula P) : comp (e A) (eInverse A) = id _ := by
  apply coherence
  change (Term.comp (eTerm A) (eInverseTerm A)).relation = (Term.id _).relation
  funext x y
  cases x <;> cases y <;> simp [eTerm,eInverseTerm,sectionTerm,sourceConjTerm]

theorem eInverse_e (A : Formula P) : comp (eInverse A) (e A) = id _ := by
  apply coherence
  change (Term.comp (eInverseTerm A) (eTerm A)).relation = (Term.id _).relation
  funext x y
  cases x with
  | inl x =>
    cases y with
    | inl y => simp [eTerm,eInverseTerm,sectionTerm,sourceConjTerm]
    | inr y => cases y with | inl y => simp [eTerm,eInverseTerm,sectionTerm,sourceConjTerm] | inr y => cases y
  | inr x =>
    cases x with
    | inl x =>
      cases y with
      | inl y => simp [eTerm,eInverseTerm,sectionTerm,sourceConjTerm]
      | inr y => cases y with | inl y => simp [eTerm,eInverseTerm,sectionTerm,sourceConjTerm] | inr y => cases y
    | inr x => cases x

end DosenPetric.Presentation.ShortProof
