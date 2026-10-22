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

def pair {X : Type u} {Y : Type v} {Z : Type w} (r : Rel X Y) (s : Rel X Z) :
    Rel X (Sum Y Z)
  | x, .inl y => r x y
  | x, .inr z => s x z

theorem comp_assoc {W X Y Z : Type u} (r : Rel W X) (s : Rel X Y) (t : Rel Y Z) :
    comp (comp r s) t = comp r (comp s t) := by
  funext w z
  apply propext
  constructor
  · rintro ⟨y, ⟨x, hr, hs⟩, ht⟩
    exact ⟨x, hr, y, hs, ht⟩
  · rintro ⟨x, hr, y, hs, ht⟩
    exact ⟨y, ⟨x, hr, hs⟩, ht⟩

theorem id_comp {X Y : Type u} (r : Rel X Y) : comp (graph id) r = r := by
  funext x y
  apply propext
  simp [comp, graph]

theorem comp_id {X Y : Type u} (r : Rel X Y) : comp r (graph id) = r := by
  funext x y
  apply propext
  simp [comp, graph]

theorem empty_comp {X Y Z : Type u} (r : Rel Y Z) :
    comp (empty : Rel X Y) r = empty := by
  funext x z
  apply propext
  simp [comp, empty]

theorem comp_empty {X Y Z : Type u} (r : Rel X Y) :
    comp r (empty : Rel Y Z) = empty := by
  funext x z
  apply propext
  simp [comp, empty]

theorem pair_fst {X Y Z : Type u} (r : Rel X Y) (s : Rel X Z) :
    comp (pair r s) fstRel = r := by
  funext x y
  apply propext
  simp [comp, pair, fstRel, Sum.exists]

theorem pair_snd {X Y Z : Type u} (r : Rel X Y) (s : Rel X Z) :
    comp (pair r s) sndRel = s := by
  funext x z
  apply propext
  simp [comp, pair, sndRel, Sum.exists]

theorem pair_eta {X Y Z : Type u} (r : Rel X (Sum Y Z)) :
    pair (comp r fstRel) (comp r sndRel) = r := by
  funext x yz
  apply propext
  cases yz <;> simp [comp, pair, fstRel, sndRel, Sum.exists]

theorem inl_copair {X Y Z : Type u} (r : Rel X Z) (s : Rel Y Z) :
    comp (graph Sum.inl) (copair r s) = r := by
  funext x z
  apply propext
  simp [comp, graph, copair]

theorem inr_copair {X Y Z : Type u} (r : Rel X Z) (s : Rel Y Z) :
    comp (graph Sum.inr) (copair r s) = s := by
  funext y z
  apply propext
  simp [comp, graph, copair]

theorem copair_eta {X Y Z : Type u} (r : Rel (Sum X Y) Z) :
    copair (comp (graph Sum.inl) r) (comp (graph Sum.inr) r) = r := by
  funext xy z
  apply propext
  cases xy <;> simp [comp, graph, copair]

theorem pair_map {X Y X' Y' : Type u} (r : Rel X X') (s : Rel Y Y') :
    pair (comp fstRel r) (comp sndRel s) = sumMap r s := by
  funext xy xy'
  apply propext
  cases xy <;> cases xy' <;> simp [pair, comp, fstRel, sndRel, sumMap]

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
