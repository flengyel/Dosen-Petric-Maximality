module

public import DosenPetric.SubstitutionFiberGraphs

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation.Term
universe u v
variable {P : Type u} {R : Type v}

/-- The exact occurrence-block square for a raw source arrow and substitution. -/
def SubstitutionCompatible (σ : P → Formula R) {A B : Formula P} (t : Term P A B) : Prop :=
  ∀ (x : A.Block σ) (y : B.Block σ),
    (t.subst σ).relation (A.contract σ x) (B.contract σ y) ↔
      Relations.Fiber.lift (fun p => (σ p).Occ) A.label B.label t.relation x y

theorem substitution_id (σ : P → Formula R) (A : Formula P) :
    SubstitutionCompatible σ (.id A) := by
  intro x y
  exact (Formula.fiber_identity σ A x y).symm

theorem substitution_empty (σ : P → Formula R) {A B : Formula P} (t : Term P A B)
    (h : t.relation = Relations.empty) (hs : (t.subst σ).relation = Relations.empty) :
    SubstitutionCompatible σ t := by
  intro x y
  rw [h,hs]
  exact ⟨False.elim,fun h => (Relations.Fiber.lift_empty (fun p => (σ p).Occ) A.label B.label x y) h⟩

theorem substitution_zero (σ : P → Formula R) (A : Formula P) :
    SubstitutionCompatible σ (.zero A) := substitution_empty σ _ rfl rfl

theorem substitution_graph (σ : P → Formula R) {A B : Formula P} (t : Term P A B)
    (f : A.Occ → B.Occ) (g : (A.subst σ).Occ → (B.subst σ).Occ)
    (h : t.relation = Relations.graph f) (hs : (t.subst σ).relation = Relations.graph g)
    (labels : ∀ x, A.label x = B.label (f x))
    (square : ∀ x : A.Block σ, g (A.contract σ x) =
      B.contract σ (Relations.Fiber.map (fun p => (σ p).Occ) A.label B.label f labels x)) :
    SubstitutionCompatible σ t := by
  intro x y
  rw [h,hs]
  exact Formula.graph_coordinates σ A B f g labels square x y

theorem substitution_comp (σ : P → Formula R) {A B C : Formula P}
    (f : Term P A B) (g : Term P B C)
    (hf : SubstitutionCompatible σ f) (hg : SubstitutionCompatible σ g) :
    SubstitutionCompatible σ (.comp f g) := by
  intro x z
  change Relations.comp (f.subst σ).relation (g.subst σ).relation
    (A.contract σ x) (C.contract σ z) ↔
      Relations.Fiber.lift (fun p => (σ p).Occ) A.label C.label (Relations.comp f.relation g.relation) x z
  rw [Relations.Fiber.lift_composition (fun p => (σ p).Occ) A.label B.label C.label f.relation g.relation
    (fun x y h => occurrence_label (ofTerm f) x y h)]
  constructor
  · rintro ⟨y,h₁,h₂⟩
    refine ⟨B.expand σ y,?_,?_⟩
    · apply (hf x (B.expand σ y)).mp
      simpa only [Formula.contract_expand] using h₁
    · apply (hg (B.expand σ y) z).mp
      simpa only [Formula.contract_expand] using h₂
  · rintro ⟨y,h₁,h₂⟩
    exact ⟨B.contract σ y,(hf x y).mpr h₁,(hg y z).mpr h₂⟩

theorem substitution_tensor (σ : P → Formula R) (o : Op) {A B C D : Formula P}
    (f : Term P A C) (g : Term P B D)
    (hf : SubstitutionCompatible σ f) (hg : SubstitutionCompatible σ g) :
    SubstitutionCompatible σ (.tensor o f g) := by
  intro x y
  cases o with
  | conj =>
    rcases x with ⟨x,a⟩
    rcases y with ⟨y,b⟩
    cases x with
    | inl x => cases y with
      | inl y => exact hf ⟨x,a⟩ ⟨y,b⟩
      | inr y => simp [subst,relation,Formula.contract,Relations.sumMap,Relations.Fiber.lift]
    | inr x => cases y with
      | inl y => simp [subst,relation,Formula.contract,Relations.sumMap,Relations.Fiber.lift]
      | inr y => exact hg ⟨x,a⟩ ⟨y,b⟩
  | disj =>
    rcases x with ⟨x,a⟩
    rcases y with ⟨y,b⟩
    cases x with
    | inl x => cases y with
      | inl y => exact hf ⟨x,a⟩ ⟨y,b⟩
      | inr y => simp [subst,relation,Formula.contract,Relations.sumMap,Relations.Fiber.lift]
    | inr x => cases y with
      | inl y => simp [subst,relation,Formula.contract,Relations.sumMap,Relations.Fiber.lift]
      | inr y => exact hg ⟨x,a⟩ ⟨y,b⟩

end DosenPetric.Presentation.Term
