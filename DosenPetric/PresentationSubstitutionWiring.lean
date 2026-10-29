module

public import DosenPetric.PresentationSubstitutionCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation.Term
universe u v
variable {P : Type u} {R : Type v}

theorem substitution_assocR (σ : P → Formula R) (o : Op) (A B C : Formula P) :
    SubstitutionCompatible σ (.assocR o A B C) := by
  cases o <;> refine substitution_graph σ _ Relations.reassoc Relations.reassoc rfl rfl
    (by intro x; rcases x with x | (x | x) <;> rfl) ?_
  all_goals intro x; rcases x with ⟨x,a⟩; rcases x with x | (x | x) <;> rfl

theorem substitution_assocL (σ : P → Formula R) (o : Op) (A B C : Formula P) :
    SubstitutionCompatible σ (.assocL o A B C) := by
  cases o <;> refine substitution_graph σ _ Occurrence.unassoc Occurrence.unassoc rfl rfl
    (by intro x; rcases x with (x | x) | x <;> rfl) ?_
  all_goals intro x; rcases x with ⟨x,a⟩; rcases x with (x | x) | x <;> rfl

theorem substitution_swap (σ : P → Formula R) (o : Op) (A B : Formula P) :
    SubstitutionCompatible σ (.swap o A B) := by
  cases o <;> refine substitution_graph σ _ Occurrence.exchange Occurrence.exchange rfl rfl
    (by intro x; cases x <;> rfl) ?_
  all_goals intro x; rcases x with ⟨x,a⟩; cases x <;> rfl

theorem substitution_inl (σ : P → Formula R) (A B : Formula P) :
    SubstitutionCompatible σ (.inl A B) := by
  refine substitution_graph σ _ Sum.inl Sum.inl rfl rfl (fun _ => rfl) ?_
  intro x
  rcases x with ⟨x,a⟩
  rfl

theorem substitution_inr (σ : P → Formula R) (A B : Formula P) :
    SubstitutionCompatible σ (.inr A B) := by
  refine substitution_graph σ _ Sum.inr Sum.inr rfl rfl (fun _ => rfl) ?_
  intro x
  rcases x with ⟨x,a⟩
  rfl

theorem substitution_codiag (σ : P → Formula R) (A : Formula P) :
    SubstitutionCompatible σ (.codiag A) := by
  refine substitution_graph σ _ (Sum.elim _root_.id _root_.id) (Sum.elim _root_.id _root_.id)
    (by funext x y; cases x <;> rfl) (by funext x y; cases x <;> rfl)
    (by intro x; cases x <;> rfl) ?_
  intro x
  rcases x with ⟨x,a⟩
  cases x <;> rfl

theorem substitution_rightIn (σ : P → Formula R) (o : Op) (A : Formula P) :
    SubstitutionCompatible σ (.rightIn o A) := by
  cases o <;> refine substitution_graph σ _ Sum.inl Sum.inl rfl rfl (fun _ => rfl) ?_
  all_goals intro x; rcases x with ⟨x,a⟩; rfl

theorem substitution_leftIn (σ : P → Formula R) (o : Op) (A : Formula P) :
    SubstitutionCompatible σ (.leftIn o A) := by
  cases o <;> refine substitution_graph σ _ Sum.inr Sum.inr rfl rfl (fun _ => rfl) ?_
  all_goals intro x; rcases x with ⟨x,a⟩; rfl

theorem substitution_rightOut (σ : P → Formula R) (o : Op) (A : Formula P) :
    SubstitutionCompatible σ (.rightOut o A) := by
  cases o <;> refine substitution_graph σ _ Occurrence.dropRight Occurrence.dropRight rfl rfl
    (by intro x; cases x with | inl x => rfl | inr x => exact Empty.elim x) ?_
  all_goals
    intro x
    rcases x with ⟨x,a⟩
    cases x with | inl x => rfl | inr x => exact Empty.elim x

theorem substitution_leftOut (σ : P → Formula R) (o : Op) (A : Formula P) :
    SubstitutionCompatible σ (.leftOut o A) := by
  cases o <;> refine substitution_graph σ _ Occurrence.dropLeft Occurrence.dropLeft rfl rfl
    (by intro x; cases x with | inl x => exact Empty.elim x | inr x => rfl) ?_
  all_goals
    intro x
    rcases x with ⟨x,a⟩
    cases x with | inl x => exact Empty.elim x | inr x => rfl

theorem substitution_mix (σ : P → Formula R) (A B : Formula P) :
    SubstitutionCompatible σ (.mix A B) := by
  refine substitution_graph σ _ _root_.id _root_.id rfl rfl (by intro x; cases x <;> rfl) ?_
  intro x
  rcases x with ⟨x,a⟩
  cases x <;> rfl

theorem substitution_dist (σ : P → Formula R) (A B C : Formula P) :
    SubstitutionCompatible σ (.dist A B C) := by
  refine substitution_graph σ _ Relations.reassoc Relations.reassoc rfl rfl
    (by intro x; rcases x with x | (x | x) <;> rfl) ?_
  intro x
  rcases x with ⟨x,a⟩
  rcases x with x | (x | x) <;> rfl

end DosenPetric.Presentation.Term
