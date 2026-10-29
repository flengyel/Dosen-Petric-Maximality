module

public import DosenPetric.PatternSubstitutionOrdinals
public import DosenPetric.PresentationSubstitutionActionQuotient

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation.ManuscriptSubstitution
universe u v
variable {P : Type u} {R : Type v}

def context (L : Formula P) : Hom (.conj L .bot) (.disj L .top) := comp (fst L .bot) (inl L .top)

/-- The positive-literal substitution has precisely the printed endpoints. -/
theorem positive_context (p : P) (A : Formula R) :
    substitute (fun _ : P => A) (context (.var p)) = context A := rfl

/-- For a negative isolated literal, p maps to neg A and the outer negation
therefore gives neg neg A before the proved double-negation retraction. -/
theorem negative_context (p : P) (A : Formula R) :
    substitute (fun _ : P => .neg A) (context (.neg (.var p))) = context (.neg (.neg A)) := rfl

def positiveLeftBlock (p : P) (A : Formula R) (x : A.Occ) :
    (Formula.conj (.var p) .bot).Block (fun _ : P => A) := ⟨.inl (),x⟩
def positiveRightBlock (p : P) (A : Formula R) (x : A.Occ) :
    (Formula.disj (.var p) .top).Block (fun _ : P => A) := ⟨.inl (),x⟩
def negativeLeftBlock (p : P) (A : Formula R) (x : A.Occ) :
    (Formula.conj (.neg (.var p)) .bot).Block (fun _ : P => .neg A) := ⟨.inl (),x⟩
def negativeRightBlock (p : P) (A : Formula R) (x : A.Occ) :
    (Formula.disj (.neg (.var p)) .top).Block (fun _ : P => .neg A) := ⟨.inl (),x⟩

theorem positive_left_exhaustive (p : P) (A : Formula R)
    (z : (Formula.conj (.var p) .bot).Block (fun _ : P => A)) :
    ∃ x : A.Occ, z = positiveLeftBlock p A x := by
  obtain ⟨r,t⟩ := z
  cases r with
  | inl r => cases r; exact ⟨t,rfl⟩
  | inr r => exact Empty.elim r

theorem positive_right_exhaustive (p : P) (A : Formula R)
    (z : (Formula.disj (.var p) .top).Block (fun _ : P => A)) :
    ∃ x : A.Occ, z = positiveRightBlock p A x := by
  obtain ⟨r,t⟩ := z
  cases r with
  | inl r => cases r; exact ⟨t,rfl⟩
  | inr r => exact Empty.elim r

theorem negative_left_exhaustive (p : P) (A : Formula R)
    (z : (Formula.conj (.neg (.var p)) .bot).Block (fun _ : P => .neg A)) :
    ∃ x : A.Occ, z = negativeLeftBlock p A x := by
  obtain ⟨r,t⟩ := z
  cases r with
  | inl r => cases r; exact ⟨t,rfl⟩
  | inr r => exact Empty.elim r

theorem negative_right_exhaustive (p : P) (A : Formula R)
    (z : (Formula.disj (.neg (.var p)) .top).Block (fun _ : P => .neg A)) :
    ∃ x : A.Occ, z = negativeRightBlock p A x := by
  obtain ⟨r,t⟩ := z
  cases r with
  | inl r => cases r; exact ⟨t,rfl⟩
  | inr r => exact Empty.elim r

theorem positive_left_contract (p : P) (A : Formula R) (x : A.Occ) :
    Formula.contract (fun _ : P => A) (.conj (.var p) .bot) (positiveLeftBlock p A x) = .inl x := rfl

theorem positive_right_contract (p : P) (A : Formula R) (x : A.Occ) :
    Formula.contract (fun _ : P => A) (.disj (.var p) .top) (positiveRightBlock p A x) = .inl x := rfl

theorem negative_left_contract (p : P) (A : Formula R) (x : A.Occ) :
    Formula.contract (fun _ : P => .neg A) (.conj (.neg (.var p)) .bot) (negativeLeftBlock p A x) = .inl x := rfl

theorem negative_right_contract (p : P) (A : Formula R) (x : A.Occ) :
    Formula.contract (fun _ : P => .neg A) (.disj (.neg (.var p)) .top) (negativeRightBlock p A x) = .inl x := rfl

theorem negative_context_to_formula (Q : Congruence (operations P)) (A : Formula P)
    (h : ContextualCollapse.K Q (Z:=zeroIdentity P) (.neg (.neg A))) :
    ContextualCollapse.K Q (Z:=zeroIdentity P) A :=
  ContextualCollapse.context_retract Q ((doubleNegation P).into A)
    ((doubleNegation P).out A) ((doubleNegation P).into_out A) h

/-- The exact positive branch of Proposition 4.2. -/
theorem positive_all_contexts (Q : Congruence (operations P))
    (closed : (substitution P).Closed Q) (p : P)
    (h : ContextualCollapse.K Q (Z:=zeroIdentity P) (.var p)) :
    ∀ A, ContextualCollapse.K Q (Z:=zeroIdentity P) A :=
  ContextualCollapse.all_contexts Q (substitution P) (doubleNegation P) closed (.pos p) h

/-- The exact negative branch, including the actual double-negation retraction. -/
theorem negative_all_contexts (Q : Congruence (operations P))
    (closed : (substitution P).Closed Q) (p : P)
    (h : ContextualCollapse.K Q (Z:=zeroIdentity P) (.neg (.var p))) :
    ∀ A, ContextualCollapse.K Q (Z:=zeroIdentity P) A :=
  ContextualCollapse.all_contexts Q (substitution P) (doubleNegation P) closed (.neg p) h

end DosenPetric.Presentation.ManuscriptSubstitution
