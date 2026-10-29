module
import DosenPetric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
namespace PositiveCoherenceChecks
example {P : Type u} : PositiveCoherence P := positive_coherence
example {P : Type u} : Faithful P := Reduced.faithful
example {P : Type u} : OccurrenceInterpretation (Presentation.operations P) (Presentation.zeroIdentity P) :=
  Presentation.interpretation P
example {P : Type u} : SignedLabelPreservation (Presentation.interpretation P) :=
  Presentation.interpretation_signedLabel P
example : (Presentation.operations Nat).fst (.var 0) (.var 0) ≠
    (Presentation.operations Nat).snd (.var 0) (.var 0) := Presentation.nonthin 0
example : ¬ Nonempty ((Presentation.category Empty).Hom .top .bot) := Presentation.empty_hom Empty
example {P : Type u} {A B : Formula P} (f g : Presentation.Hom A B)
    (h : Presentation.occurrenceMap f = Presentation.occurrenceMap g) : f = g := Presentation.coherence h
example : ofTerm (P:=Empty) (Term.id .top) = ofTerm (Term.zero .top) := by
  apply Reduced.faithful
  funext x y
  cases x
example : ofTerm (Term.id (P:=Nat) (.lit (.neg 0))) ≠ ofTerm (Term.zero (.lit (.neg 0))) := by
  intro h
  have hx : occurrenceMap (ofTerm (Term.id (P:=Nat) (.lit (.neg 0))))
      (Literal.neg 0).point (Literal.neg 0).point := rfl
  rw [h] at hx
  exact hx

example {P : Type u} {A B : NormalForm P} (t : Term P A B)
    (ht : t.Positive) :
    ∃ g : G P [A] [B], g.CutFree ∧ g.Atomized ∧
      ofTerm g.denote = comp (rightOut .conj A) (comp (ofTerm t) (rightIn .disj B)) ∧
      ∀ (x : A.formula.Occ) (y : B.formula.Occ),
        g.relation (singletonOcc .conj A x) (singletonOcc .disj B y) ↔ t.relation x y :=
  positive_cutFree_represented t ht

example {P : Type u} {A B : NormalForm P} (t : Term P A B)
    (ht : t.Positive) (hA : Pure .conj A) (hB : Pure .disj B) :
    ∃ g : G P [A] [B], g.CutFree ∧ g.Atomized ∧ g.MixOnly ∧
      ofTerm g.denote = comp (rightOut .conj A) (comp (ofTerm t) (rightIn .disj B)) ∧
      ∀ (x : A.formula.Occ) (y : B.formula.Occ),
        g.relation (singletonOcc .conj A x) (singletonOcc .disj B y) ↔ t.relation x y :=
  positive_mix_represented t ht hA hB

example {P : Type u} {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (hg : g.MixOnly) :
    HasPureNormalForm (ofTerm g.denote) :=
  G.mix_normal_form g hg

example {P : Type u} {A B : NormalForm P} (f g : Term P A B)
    (hf : f.Positive) (hg : g.Positive) (hA : Pure .conj A) (hB : Pure .disj B)
    (h : f.relation = g.relation) : ofTerm f = ofTerm g :=
  pure_positive_coherence f g hf hg hA hB h

example {P : Type u} {A B : NormalForm P} (d : DNF A) (c : CNF B)
    (f g : Term P A B) (hf : f.Positive) (hg : g.Positive)
    (h : f.relation = g.relation) : ofTerm f = ofTerm g :=
  normal_positive_coherence d c f g hf hg h

example {P : Type u} (A : NormalForm P) :
    ∃ (B : NormalForm P) (_ : NormalRetract A B), DNF B :=
  dnf_expansion A

example {P : Type u} (A : NormalForm P) :
    ∃ (B : NormalForm P) (_ : NormalRetract A B), CNF B :=
  cnf_expansion A

example {P : Type u} {A B : NormalForm P} (f g : Hom A B)
    (hf : Represented f) (hg : Represented g) (h : occurrenceMap f = occurrenceMap g) : f = g :=
  represented_coherence f g hf hg h

example {P : Type u} (l : Literal P) :
    (PurePort.left (.lit l) (PurePort.here l) : PurePort .conj (.conj (.lit l) (.lit l)) l).position ≠
    (PurePort.right (.lit l) (PurePort.here l) : PurePort .conj (.conj (.lit l) (.lit l)) l).position := by
  intro h
  simp only [PurePort.position] at h
  cases h
example {P : Type u} (l : Literal P) :
    occurrenceMap (PureEdge.arrow (P:=P) (A:=.lit l) (B:=.disj (.lit l) (.lit l))
      ⟨l,.here l,.left (.lit l) (.here l)⟩) l.point (Sum.inl l.point) := by
  rw [PureEdge.relation]
  exact ⟨rfl,rfl⟩
example (w : Hom (P:=Empty) .top .top) : finiteUnion w [] = zeroOf w := rfl
example (l : Literal Nat) :
    ∃ g : G Nat [.lit l] [.lit l], g.CutFree ∧ g.Atomized ∧
      ofTerm g.denote = comp (rightOut .conj (.lit l))
        (comp (ofTerm (Term.id (.lit l))) (rightIn .disj (.lit l))) ∧
      ∀ x y, g.relation (singletonOcc .conj (.lit l) x) (singletonOcc .disj (.lit l) y) ↔
        (Term.id (.lit l)).relation x y := positive_cutFree_represented _ (.id _)
end PositiveCoherenceChecks

#print axioms DosenPetric.Reduced.Gentzen.positive_coherence

#print axioms DosenPetric.Reduced.faithful

#print axioms DosenPetric.Reduced.boolean_coherence

#print axioms DosenPetric.Presentation.coherence

#print axioms DosenPetric.Presentation.interpretation

#print axioms DosenPetric.Presentation.interpretation_signedLabel

#print axioms DosenPetric.Reduced.Gentzen.G.mix_normal_form

#print axioms DosenPetric.Reduced.Gentzen.G.pure_cutFree_faithful

#print axioms DosenPetric.Reduced.Gentzen.normal_positive_coherence

#print axioms DosenPetric.Reduced.Gentzen.dnf_expansion

#print axioms DosenPetric.Reduced.Gentzen.cnf_expansion

#print axioms DosenPetric.Reduced.Gentzen.PureEdge.evaluate_faithful

#print axioms DosenPetric.Reduced.finiteUnion.eq_of_members
