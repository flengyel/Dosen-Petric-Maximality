module

public import DosenPetric.PresentationNegationOccurrence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation.ShortProof
universe u
variable {P : Type u}

/-- The manuscript's particular q_A, in execution order. -/
def qTerm (A : Formula P) : Term P (.disj (.conj A .bot) .top) (.disj A .top) :=
  Term.copair (.comp (.fst A .bot) (.inl A .top)) (.inr A .top)

/-- An explicit inverse, using the original distributor and units. -/
def qInverseTerm (A : Formula P) : Term P (.disj A .top) (.disj (.conj A .bot) .top) :=
  Term.copair (.comp (.rightIn .conj A)
    (.comp (.tensor .conj (.id A) (.inr .bot .top)) (.dist A .bot .top)))
    (.inr (.conj A .bot) .top)

def q (A : Formula P) : Hom (.disj (.conj A .bot) .top) (.disj A .top) := ofTerm (qTerm A)
def qInverse (A : Formula P) : Hom (.disj A .top) (.disj (.conj A .bot) .top) := ofTerm (qInverseTerm A)

theorem q_definition (A : Formula P) :
    q A = copair (comp (fst A .bot) (inl A .top)) (inr A .top) := rfl

attribute [local simp] Term.relation Relations.comp Relations.graph Relations.sumMap
  Relations.pair Relations.copair Relations.fstRel Relations.sndRel Relations.reassoc
  Occurrence.dropRight Sum.exists Term.copair

theorem q_qInverse (A : Formula P) : comp (q A) (qInverse A) = id _ := by
  apply coherence
  change (Term.comp (qTerm A) (qInverseTerm A)).relation = (Term.id _).relation
  funext x y
  cases x with
  | inl x =>
    cases x with
    | inl x =>
      cases y with
      | inl y => cases y with | inl y => simp [qTerm,qInverseTerm] | inr y => cases y
      | inr y => cases y
    | inr x => cases x
  | inr x => cases x

theorem qInverse_q (A : Formula P) : comp (qInverse A) (q A) = id _ := by
  apply coherence
  change (Term.comp (qInverseTerm A) (qTerm A)).relation = (Term.id _).relation
  funext x y
  cases x with
  | inl x => cases y with | inl y => simp [qTerm,qInverseTerm] | inr y => cases y
  | inr x => cases x

end DosenPetric.Presentation.ShortProof
