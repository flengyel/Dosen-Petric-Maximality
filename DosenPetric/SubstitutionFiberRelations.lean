module

public import DosenPetric.FormulaSubstitutionLaws

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Relations.Fiber
universe u v v' v'' w
variable {P : Type u} (K : P → Type w)

def cast {p q : P} (h : p = q) (x : K p) : K q := h ▸ x

theorem cast_self {p : P} (h : p = p) (x : K p) : cast K h x = x := by
  cases h; rfl

theorem cast_trans {p q r : P} (h : p = q) (k : q = r) (x : K p) :
    cast K k (cast K h x) = cast K (h.trans k) x := by
  cases h; cases k; rfl

def Block {X : Type v} (a : X → P) := (x : X) × K (a x)

/-- Extend a labelled relation by the identity inside each substituted block. -/
def lift {X : Type v} {Y : Type v'} (a : X → P) (b : Y → P) (r : Rel X Y) :
    Rel (Block K a) (Block K b) := fun x y =>
  ∃ h : a x.1 = b y.1, r x.1 y.1 ∧ cast K h x.2 = y.2

theorem lift_empty {X : Type v} {Y : Type v'} (a : X → P) (b : Y → P)
    (x : Block K a) (y : Block K b) : ¬ lift K a b empty x y := by
  rintro ⟨_,h,_⟩
  exact h

theorem lift_identity {X : Type v} (a : X → P) (x y : Block K a) :
    lift K a a (graph _root_.id) x y ↔ x = y := by
  constructor
  · rintro ⟨h,he,hk⟩
    rcases x with ⟨x,s⟩
    rcases y with ⟨y,t⟩
    change x = y at he
    cases he
    change cast K h s = t at hk
    rw [cast_self] at hk
    cases hk
    rfl
  · intro he
    cases he
    exact ⟨rfl,rfl,rfl⟩

theorem lift_composition {X : Type v} {Y : Type v'} {Z : Type v''}
    (a : X → P) (b : Y → P) (c : Z → P) (r : Rel X Y) (s : Rel Y Z)
    (labels : ∀ x y, r x y → a x = b y) (x : Block K a) (z : Block K c) :
    lift K a c (comp r s) x z ↔ comp (lift K a b r) (lift K b c s) x z := by
  constructor
  · rintro ⟨h,⟨y,hr,hs⟩,hk⟩
    have hm := labels x.1 y hr
    refine ⟨⟨y,cast K hm x.2⟩,⟨hm,hr,rfl⟩,⟨hm.symm.trans h,hs,?_⟩⟩
    simpa only [cast_trans] using hk
  · rintro ⟨y,⟨h,hr,he⟩,⟨k,hs,hk⟩⟩
    refine ⟨h.trans k,⟨y.1,hr,hs⟩,?_⟩
    rw [← cast_trans K h k,he]
    exact hk

theorem lift_converse {X : Type v} {Y : Type v'} (a : X → P) (b : Y → P)
    (r : Rel X Y) (x : Block K a) (y : Block K b) :
    lift K b a (fun y x => r x y) y x ↔ lift K a b r x y := by
  constructor
  · rintro ⟨h,hr,hk⟩
    refine ⟨h.symm,hr,?_⟩
    have he := congrArg (cast K h.symm) hk
    simpa only [cast_trans,cast_self] using he.symm
  · rintro ⟨h,hr,hk⟩
    refine ⟨h.symm,hr,?_⟩
    have he := congrArg (cast K h.symm) hk
    simpa only [cast_trans,cast_self] using he.symm

end DosenPetric.Relations.Fiber
