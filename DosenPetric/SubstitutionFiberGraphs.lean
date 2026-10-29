module

public import DosenPetric.FormulaSubstitutionCoordinates

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Relations.Fiber
universe u v v' w
variable {P : Type u} (K : P → Type w)

def map {X : Type v} {Y : Type v'} (a : X → P) (b : Y → P) (f : X → Y)
    (labels : ∀ x, a x = b (f x)) (x : Block K a) : Block K b :=
  ⟨f x.1,cast K (labels x.1) x.2⟩

theorem lift_graph {X : Type v} {Y : Type v'} (a : X → P) (b : Y → P) (f : X → Y)
    (labels : ∀ x, a x = b (f x)) (x : Block K a) (y : Block K b) :
    lift K a b (graph f) x y ↔ map K a b f labels x = y := by
  constructor
  · rintro ⟨h,he,hk⟩
    rcases y with ⟨y,t⟩
    change f x.1 = y at he
    cases he
    change cast K (labels x.1) x.2 = t at hk
    change (⟨f x.1,cast K (labels x.1) x.2⟩ : Block K b) = ⟨f x.1,t⟩
    cases hk
    rfl
  · intro he
    cases he
    exact ⟨labels x.1,rfl,rfl⟩

end DosenPetric.Relations.Fiber
namespace DosenPetric.Formula
universe u v
variable {P : Type u} {R : Type v}

/-- A tagged block square determines the substituted graph exactly. -/
theorem graph_coordinates (σ : P → Formula R) (A B : Formula P)
    (f : A.Occ → B.Occ) (g : (A.subst σ).Occ → (B.subst σ).Occ)
    (labels : ∀ x, A.label x = B.label (f x))
    (square : ∀ x : A.Block σ, g (A.contract σ x) =
      B.contract σ (Relations.Fiber.map (fun p => (σ p).Occ) A.label B.label f labels x))
    (x : A.Block σ) (y : B.Block σ) :
    Relations.graph g (A.contract σ x) (B.contract σ y) ↔
      Relations.Fiber.lift (fun p => (σ p).Occ) A.label B.label (Relations.graph f) x y := by
  change g (A.contract σ x) = B.contract σ y ↔ _
  rw [square]
  exact (contract_eq_iff σ B
    (Relations.Fiber.map (fun p => (σ p).Occ) A.label B.label f labels x) y).trans
      (Relations.Fiber.lift_graph (fun p => (σ p).Occ) A.label B.label f labels x y).symm

end DosenPetric.Formula
