module

public import Init

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.Relations

universe u v w u₁ v₁

abbrev Rel (X : Type u) (Y : Type v) := X → Y → Prop

def comp {X : Type u} {Y : Type v} {Z : Type w} (r : Rel X Y) (s : Rel Y Z) :
    Rel X Z := fun x z => ∃ y, r x y ∧ s y z

def graph {X : Type u} {Y : Type v} (f : X → Y) : Rel X Y := fun x y => f x = y

def empty {X : Type u} {Y : Type v} : Rel X Y := fun _ _ => False

def sumMap {X : Type u} {X' : Type u₁} {Y : Type v} {Y' : Type v₁} (r : Rel X X') (s : Rel Y Y') :
    Rel (Sum X Y) (Sum X' Y')
  | .inl x, .inl x' => r x x'
  | .inr y, .inr y' => s y y'
  | _, _ => False

def fstRel {X : Type u} {Y : Type v} : Rel (Sum X Y) X
  | .inl x, x' => x = x'
  | .inr _, _ => False

def sndRel {X : Type u} {Y : Type v} : Rel (Sum X Y) Y
  | .inl _, _ => False
  | .inr y, y' => y = y'

def copair {X : Type u} {Y : Type v} {Z : Type w} (r : Rel X Z) (s : Rel Y Z) :
    Rel (Sum X Y) Z
  | .inl x, z => r x z
  | .inr y, z => s y z

def reassoc {X : Type u} {Y : Type v} {Z : Type w} :
    Sum X (Sum Y Z) → Sum (Sum X Y) Z
  | .inl x => .inl (.inl x)
  | .inr (.inl y) => .inl (.inr y)
  | .inr (.inr z) => .inr z

def swap {X : Type u} : Sum X X → Sum X X
  | .inl x => .inr x
  | .inr x => .inl x

def fold {X : Type u} : Rel (Sum X X) X
  | .inl x, y => x = y
  | .inr x, y => x = y

/-- The relation of `d ∘ (1 ∧ ι₂)`, in tagged occurrence coordinates. -/
def uRel (X : Type u) (Y : Type v) : Rel (Sum X X) (Sum (Sum X Y) X) :=
  comp (sumMap (graph (id : X → X)) (graph (Sum.inr : X → Sum Y X))) (graph reassoc)

/-- The relation of `[π₁,1] ∘ d ∘ (1 ∧ ι₂)`. -/
def hRel (X : Type u) (Y : Type v) : Rel (Sum X X) X :=
  comp (uRel X Y) (copair fstRel (graph id))

theorem graph_comp {X : Type u} {Y : Type v} {Z : Type w} (f : X → Y) (g : Y → Z) :
    comp (graph f) (graph g) = graph (fun x => g (f x)) := by
  funext x z
  apply propext
  simp [comp, graph]

theorem hRel_eq_fold (X : Type u) (Y : Type v) : hRel X Y = fold := by
  funext x z
  apply propext
  cases x <;> simp [hRel, uRel, comp, sumMap, graph, reassoc, copair, fstRel, fold,
    Sum.exists]

theorem hRel_independent (X : Type u) (Y : Type v) (Z : Type w) :
    hRel X Y = hRel X Z := (hRel_eq_fold X Y).trans (hRel_eq_fold X Z).symm

theorem fold_swap (X : Type u) : comp (graph (@swap X)) fold = fold := by
  funext x z
  apply propext
  cases x <;> simp [comp, graph, fold, swap]

theorem hRel_swap (X : Type u) (Y : Type v) :
    comp (graph (@swap X)) (hRel X Y) = hRel X Y := by
  rw [hRel_eq_fold, fold_swap]

/-- Replacing the first copairing component by the empty relation removes the first block. -/
theorem second_block (X : Type u) (Y : Type v) :
    comp (uRel X Y) (copair empty (graph (Sum.inl : X → Sum X Empty))) =
      comp sndRel (graph (Sum.inl : X → Sum X Empty)) := by
  funext x z
  apply propext
  cases x <;> simp [uRel, comp, sumMap, graph, reassoc, copair, empty, sndRel, Sum.exists]

theorem first_injection (X : Type u) (Y : Type v) (Z : Type w) :
    comp (sumMap (graph (id : X → X)) (graph (Sum.inl : Y → Sum Y Z)))
      (graph reassoc) = graph (Sum.inl : Sum X Y → Sum (Sum X Y) Z) := by
  funext x z
  apply propext
  cases x <;> simp [comp, sumMap, graph, reassoc, Sum.exists]

theorem projections_distinct : @fstRel Unit Unit ≠ sndRel := by
  intro h
  have e := congrFun (congrFun h (.inl ())) ()
  have t : fstRel (.inl () : Sum Unit Unit) () := rfl
  exact (Eq.mp e t)

end DosenPetric.Relations
