module

public import DosenPetric.SemanticBicartesian
public import DosenPetric.SemanticInterpretationSubstitution

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.PresentationSemantics.Source
universe r w

def objects (R : Type r) : Objects (Formula R) where
  conj := Formula.conj
  disj := Formula.disj
  top := .top
  bot := .bot
  neg := Formula.neg

/-- The actual equation-generated category supplies every semantic primitive. -/
def primitives (R : Type r) : Primitives (Presentation.category R) (objects R) where
  tensor := Presentation.tensor
  assocR := Presentation.assocR
  assocL := Presentation.assocL
  swap := Presentation.swap
  diag := Presentation.diag
  codiag := Presentation.codiag
  fst := Presentation.fst
  snd := Presentation.snd
  inl := Presentation.inl
  inr := Presentation.inr
  rightOut := Presentation.rightOut
  rightIn := Presentation.rightIn
  leftOut := Presentation.leftOut
  leftIn := Presentation.leftIn
  mix := Presentation.mix
  dist := Presentation.dist
  zero := Presentation.zero
  dnOut := Presentation.dnOut
  dnIn := Presentation.dnIn
  dmConjOut := Presentation.dmConjOut
  dmConjIn := Presentation.dmConjIn
  dmDisjOut := Presentation.dmDisjOut
  dmDisjIn := Presentation.dmDisjIn
  negTopOut := Presentation.negTopOut
  negTopIn := Presentation.negTopIn
  negBotOut := Presentation.negBotOut
  negBotIn := Presentation.negBotIn
  excludedMiddle := Presentation.excludedMiddle
  contradiction := Presentation.contradiction

def identityInterpretation (R : Type r) : Interpretation (primitives R) R where
  toFunctor := Functor.identity (Presentation.category R)
  obj_top := rfl
  obj_bot := rfl
  obj_conj _ _ := rfl
  obj_disj _ _ := rfl
  obj_neg _ := rfl
  map_tensor _ {_ _ _ _} _ _ := HEq.rfl
  map_assocR _ _ _ _ := HEq.rfl
  map_assocL _ _ _ _ := HEq.rfl
  map_swap _ _ _ := HEq.rfl
  map_diag _ := HEq.rfl
  map_codiag _ := HEq.rfl
  map_fst _ _ := HEq.rfl
  map_snd _ _ := HEq.rfl
  map_inl _ _ := HEq.rfl
  map_inr _ _ := HEq.rfl
  map_rightOut _ _ := HEq.rfl
  map_rightIn _ _ := HEq.rfl
  map_leftOut _ _ := HEq.rfl
  map_leftIn _ _ := HEq.rfl
  map_mix _ _ := HEq.rfl
  map_dist _ _ _ := HEq.rfl
  map_zero _ := HEq.rfl
  map_dnOut _ := HEq.rfl
  map_dnIn _ := HEq.rfl
  map_dmConjOut _ _ := HEq.rfl
  map_dmConjIn _ _ := HEq.rfl
  map_dmDisjOut _ _ := HEq.rfl
  map_dmDisjIn _ _ := HEq.rfl
  map_negTopOut := HEq.rfl
  map_negTopIn := HEq.rfl
  map_negBotOut := HEq.rfl
  map_negBotIn := HEq.rfl
  map_excludedMiddle _ := HEq.rfl
  map_contradiction _ := HEq.rfl

/-- The intended source model satisfies every equation at every valuation,
proved through actual substitution and the interpretation/evaluation theorem. -/
theorem equations {P : Type w} (R : Type r) : (primitives R).SatisfiesTheory P := by
  intro α A B f g h
  let F := (identityInterpretation R).precompose α
  have hf := F.raw_evaluation f
  have hg := F.raw_evaluation g
  have he : F.map (Presentation.ofTerm f) = F.map (Presentation.ofTerm g) :=
    congrArg F.toFunctor.map (Presentation.equation h)
  exact eq_of_heq (hf.symm.trans ((heq_of_eq he).trans hg))

theorem bicartesian (R : Type r) : BicartesianLaws (primitives R) where
  pair_fst := (Presentation.operations R).pair_fst
  pair_snd := (Presentation.operations R).pair_snd
  pair_eta := (Presentation.operations R).pair_eta
  inl_copair := (Presentation.operations R).inl_copair
  inr_copair := (Presentation.operations R).inr_copair
  copair_eta := (Presentation.operations R).copair_eta
  toTop_unique := (Presentation.operations R).toTop_unique
  fromBot_unique := (Presentation.operations R).fromBot_unique

/-- Fully instantiated model data; no model law is left as a hypothesis. -/
theorem model (P : Type w) (R : Type r) : Model P (primitives R) where
  equations := equations R
  bicartesian := bicartesian R
  zero_identity := Presentation.Laws.zero_law

end DosenPetric.PresentationSemantics.Source
