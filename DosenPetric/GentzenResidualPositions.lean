module

public import DosenPetric.GentzenRankTwoDegreeStep

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace At
variable {Γ : List (NormalForm P)} {C E : NormalForm P}

/-- Remove another tagged slot, provided it is distinct from the deleted slot. -/
def remove {Γ : List (NormalForm P)} {C E : NormalForm P} (x : At Γ C) (b : At Γ E) (h : b.index ≠ x.index) : At x.erase E :=
  match x, b with
  | .here _ _, .here _ _ => False.elim (h rfl)
  | .here _ _, .there b => b
  | .there _, .here E _ => .here E _
  | .there x, .there b => .there (remove x b (by intro e; exact h (congrArg Nat.succ e)))

theorem retain_ne (x : At Γ C) (b : At x.erase E) : (x.retain b).index ≠ x.index := by
  rw [retain_index]
  split <;> omega

theorem retain_remove (x : At Γ C) (b : At Γ E) (h : b.index ≠ x.index) :
    x.retain (x.remove b h) = b := by
  induction x with
  | here => cases b with
    | here => exact False.elim (h rfl)
    | there => rfl
  | there x ih => cases b with
    | here => rfl
    | there b => exact congrArg At.there (ih b (by intro e; exact h (congrArg Nat.succ e)))

theorem remove_retain (x : At Γ C) (b : At x.erase E) :
    x.remove (x.retain b) (x.retain_ne b) = b := by
  induction x with
  | here => rfl
  | there x ih => cases b with
    | here => rfl
    | there b => exact congrArg At.there (ih b)

/-- Equality of ordinal positions determines the formula at that position. -/
theorem formula_eq {A B : NormalForm P} (a : At Γ A) (b : At Γ B)
    (h : a.index = b.index) : A = B := by
  induction a with
  | here => cases b with
    | here => rfl
    | there b => simp only [index] at h; omega
  | there a ih => cases b with
    | here => simp only [index] at h; omega
    | there b => exact ih b (by simp only [index] at h; omega)

end At
namespace Route
variable {K U : List (NormalForm P)}

/-- Construct a route from its typed map on all occurrence tags. -/
def tabulate (K : List (NormalForm P)) : (U : List (NormalForm P)) →
    ({A : NormalForm P} → At U A → At K A) → Route K U
  | [], _ => .nil
  | A :: U, f => .cons (f (.here A U)) (tabulate K U (fun a => f a.there))

theorem get_tabulate (f : {A : NormalForm P} → At U A → At K A)
    {A : NormalForm P} (a : At U A) : (tabulate K U f).get a = f a := by
  induction a with
  | here => rfl
  | there a ih => exact ih (fun a => f a.there)

end Route
end DosenPetric.Reduced.Gentzen
