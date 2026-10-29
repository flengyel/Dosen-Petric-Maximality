module

public import DosenPetric.PresentationSubstitutionWiring

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation.Term
universe u v
variable {P : Type u} {R : Type v}

/-- A converse comparison is used only for these explicitly constructed relations. -/
theorem substitution_converse (σ : P → Formula R) {A B : Formula P}
    (t : Term P A B) (s : Term P B A)
    (h : ∀ x y, t.relation x y ↔ s.relation y x)
    (hs : ∀ x y, (t.subst σ).relation x y ↔ (s.subst σ).relation y x)
    (hc : SubstitutionCompatible σ s) : SubstitutionCompatible σ t := by
  intro x y
  have he : s.relation = (fun y x => t.relation x y) := by
    funext y x
    exact propext (h x y).symm
  have hh := hc y x
  rw [he] at hh
  exact (hs _ _).trans (hh.trans (Relations.Fiber.lift_converse
    (fun p => (σ p).Occ) A.label B.label t.relation x y))

/-- Converse wiring uses occurrence functions with their actual formula labels;
it does not identify product and coproduct endpoint formulas. -/
theorem substitution_converse_graph (σ : P → Formula R) {A B : Formula P} (t : Term P A B)
    (f : B.Occ → A.Occ) (g : (B.subst σ).Occ → (A.subst σ).Occ)
    (h : ∀ x y, t.relation x y ↔ f y = x)
    (hs : ∀ x y, (t.subst σ).relation x y ↔ g y = x)
    (labels : ∀ y, B.label y = A.label (f y))
    (square : ∀ y : B.Block σ, g (B.contract σ y) =
      A.contract σ (Relations.Fiber.map (fun p => (σ p).Occ) B.label A.label f labels y)) :
    SubstitutionCompatible σ t := by
  intro x y
  have he : Relations.graph f = (fun y x => t.relation x y) := by
    funext y x
    exact propext (h x y).symm
  have hh := Formula.graph_coordinates σ B A f g labels square y x
  rw [he] at hh
  exact (hs _ _).trans (hh.trans (Relations.Fiber.lift_converse
    (fun p => (σ p).Occ) A.label B.label t.relation x y))

theorem substitution_fst (σ : P → Formula R) (A B : Formula P) :
    SubstitutionCompatible σ (.fst A B) := by
  refine substitution_converse_graph σ _ Sum.inl Sum.inl
    (by intro x y; cases x <;> simp [relation,Relations.fstRel,eq_comm])
    (by
      intro x y
      cases x <;> simp [subst,relation,Relations.fstRel,eq_comm]
      constructor <;> intro h <;> first | exact congrArg Sum.inl h | exact Sum.inl.inj h) (fun _ => rfl) ?_
  intro x
  rcases x with ⟨x,a⟩
  rfl

theorem substitution_snd (σ : P → Formula R) (A B : Formula P) :
    SubstitutionCompatible σ (.snd A B) := by
  refine substitution_converse_graph σ _ Sum.inr Sum.inr
    (by intro x y; cases x <;> simp [relation,Relations.sndRel,eq_comm])
    (by
      intro x y
      cases x <;> simp [subst,relation,Relations.sndRel,eq_comm]
      constructor <;> intro h <;> first | exact congrArg Sum.inr h | exact Sum.inr.inj h) (fun _ => rfl) ?_
  intro x
  rcases x with ⟨x,a⟩
  rfl

theorem substitution_diag (σ : P → Formula R) (A : Formula P) :
    SubstitutionCompatible σ (.diag A) := by
  refine substitution_converse_graph σ _ (Sum.elim _root_.id _root_.id) (Sum.elim _root_.id _root_.id)
    (by intro x y; cases y <;> simp [relation,Relations.pair,Relations.graph,eq_comm])
    (by intro x y; cases y <;> simp [subst,relation,Relations.pair,Relations.graph,eq_comm])
    (by intro y; cases y <;> rfl) ?_
  intro y
  rcases y with ⟨y,a⟩
  cases y <;> rfl

theorem substitution_dnOut (σ : P → Formula R) (A : Formula P) :
    SubstitutionCompatible σ (.dnOut A) := by
  intro x y
  exact (Formula.fiber_identity σ A x y).symm

theorem substitution_dnIn (σ : P → Formula R) (A : Formula P) :
    SubstitutionCompatible σ (.dnIn A) := by
  intro x y
  exact (Formula.fiber_identity σ A x y).symm

theorem substitution_dmConjOut (σ : P → Formula R) (A B : Formula P) :
    SubstitutionCompatible σ (.dmConjOut A B) := by
  refine substitution_graph σ _ _root_.id _root_.id rfl rfl (by intro x; cases x <;> rfl) ?_
  intro x
  rcases x with ⟨x,a⟩
  cases x <;> rfl

theorem substitution_dmConjIn (σ : P → Formula R) (A B : Formula P) :
    SubstitutionCompatible σ (.dmConjIn A B) := by
  refine substitution_graph σ _ _root_.id _root_.id rfl rfl (by intro x; cases x <;> rfl) ?_
  intro x
  rcases x with ⟨x,a⟩
  cases x <;> rfl

theorem substitution_dmDisjOut (σ : P → Formula R) (A B : Formula P) :
    SubstitutionCompatible σ (.dmDisjOut A B) := by
  refine substitution_graph σ _ _root_.id _root_.id rfl rfl (by intro x; cases x <;> rfl) ?_
  intro x
  rcases x with ⟨x,a⟩
  cases x <;> rfl

theorem substitution_dmDisjIn (σ : P → Formula R) (A B : Formula P) :
    SubstitutionCompatible σ (.dmDisjIn A B) := by
  refine substitution_graph σ _ _root_.id _root_.id rfl rfl (by intro x; cases x <;> rfl) ?_
  intro x
  rcases x with ⟨x,a⟩
  cases x <;> rfl

theorem substitution_negTopOut (σ : P → Formula R) : SubstitutionCompatible σ .negTopOut := by
  intro x y
  exact Empty.elim x.1

theorem substitution_negTopIn (σ : P → Formula R) : SubstitutionCompatible σ .negTopIn := by
  intro x y
  exact Empty.elim x.1

theorem substitution_negBotOut (σ : P → Formula R) : SubstitutionCompatible σ .negBotOut := by
  intro x y
  exact Empty.elim x.1

theorem substitution_negBotIn (σ : P → Formula R) : SubstitutionCompatible σ .negBotIn := by
  intro x y
  exact Empty.elim x.1

theorem substitution_excludedMiddle (σ : P → Formula R) (A : Formula P) :
    SubstitutionCompatible σ (.excludedMiddle A) := by
  intro x y
  exact Empty.elim x.1

theorem substitution_contradiction (σ : P → Formula R) (A : Formula P) :
    SubstitutionCompatible σ (.contradiction A) := by
  intro x y
  exact Empty.elim y.1

end DosenPetric.Presentation.Term
