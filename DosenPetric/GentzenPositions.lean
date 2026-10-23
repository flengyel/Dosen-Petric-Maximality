module

public import DosenPetric.GentzenRouteComponents

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace At

def index {Γ : List (NormalForm P)} {A : NormalForm P} : At Γ A → Nat
  | .here _ _ => 0
  | .there a => a.index + 1

theorem index_lt {Γ : List (NormalForm P)} {A : NormalForm P} (a : At Γ A) : a.index < Γ.length := by
  induction a with
  | here => simp only [index, List.length_cons]; omega
  | there a ih => simp only [index, List.length_cons]; omega

theorem index_injective {Γ : List (NormalForm P)} {A : NormalForm P} (a b : At Γ A)
    (h : a.index = b.index) : a = b := by
  induction a with
  | here => cases b with
    | here => rfl
    | there b => simp only [index] at h; omega
  | there a ih => cases b with
    | here => simp only [index] at h; omega
    | there b => exact congrArg At.there (ih b (by simpa only [index, Nat.add_right_cancel_iff] using h))

theorem index_before {Γ : List (NormalForm P)} {A : NormalForm P} (a : At Γ A) (Δ : List (NormalForm P)) :
    (a.before Δ).index = a.index := by
  induction a with
  | here => rfl
  | there a ih => exact congrArg (fun n => n + 1) ih

theorem index_shift (Γ : List (NormalForm P)) {Δ : List (NormalForm P)} {A : NormalForm P} (a : At Δ A) :
    (At.shift Γ a).index = Γ.length + a.index := by
  induction Γ with
  | nil => simp only [At.shift, List.length_nil, Nat.zero_add]
  | cons B Γ ih => simp only [At.shift, index, List.length_cons, ih]; omega

def cast {Γ Δ : List (NormalForm P)} (h : Γ = Δ) {A : NormalForm P} (a : At Γ A) : At Δ A := h ▸ a

theorem index_cast {Γ Δ : List (NormalForm P)} (h : Γ = Δ) {A : NormalForm P} (a : At Γ A) :
    (a.cast h).index = a.index := by cases h; rfl
end At

namespace Route

def cast {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ') (w : Route Γ Δ) : Route Γ' Δ' :=
  hΓ ▸ hΔ ▸ w

theorem cast_heq {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ') (w : Route Γ Δ) :
    (w.cast hΓ hΔ) ≍ w := by cases hΓ; cases hΔ; rfl

theorem get_index_cast {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ') (w : Route Γ Δ)
    {A : NormalForm P} (a : At Δ' A) :
    ((w.cast hΓ hΔ).get a).index = (w.get (a.cast hΔ.symm)).index := by
  cases hΓ; cases hΔ; rfl

theorem get_append_before {Γ Δ Θ : List (NormalForm P)} (w : Route Γ Δ) (v : Route Γ Θ)
    {A : NormalForm P} (a : At Δ A) : (w.append v).get (a.before Θ) = w.get a := by
  induction a with
  | here => cases w; rfl
  | there a ih => cases w with | cons b w => exact ih w

theorem get_append_shift {Γ Δ Θ : List (NormalForm P)} (w : Route Γ Δ) (v : Route Γ Θ)
    {A : NormalForm P} (a : At Θ A) : (w.append v).get (At.shift Δ a) = v.get a := by
  induction w with
  | nil => rfl
  | cons b w ih => exact ih

end Route
end DosenPetric.Reduced.Gentzen
