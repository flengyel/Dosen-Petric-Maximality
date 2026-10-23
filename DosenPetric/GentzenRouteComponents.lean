module

public import DosenPetric.GentzenExchangeComponents

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace At

theorem cases_append (Γ Δ : List (NormalForm P)) {A : NormalForm P} (a : At (Γ ++ Δ) A) :
    (∃ b : At Γ A, a = b.before Δ) ∨ (∃ b : At Δ A, a = At.shift Γ b) := by
  induction Γ with
  | nil => exact .inr ⟨a, rfl⟩
  | cons B Γ ih =>
    cases a with
    | here => exact .inl ⟨.here _ Γ, rfl⟩
    | there a =>
      cases ih a with
      | inl h => obtain ⟨b, rfl⟩ := h; exact .inl ⟨b.there, rfl⟩
      | inr h => obtain ⟨b, rfl⟩ := h; exact .inr ⟨b, rfl⟩


end At

namespace Route

theorem get_map {Γ Θ Δ : List (NormalForm P)}
    (f : {A : NormalForm P} → At Γ A → At Θ A) (w : Route Γ Δ)
    {A : NormalForm P} (a : At Δ A) : (w.map f).get a = f (w.get a) := by
  induction a with
  | here => cases w; rfl
  | there a ih => cases w with | cons b w => exact ih w

theorem get_identity {Γ : List (NormalForm P)} {A : NormalForm P} (a : At Γ A) :
    (identity Γ).get a = a := by
  induction a with
  | here => rfl
  | there a ih => simpa only [identity, get, get_map] using congrArg At.there ih

def sideArrow (o : Op) {Γ Δ : List (NormalForm P)} (w : Route Γ Δ) :
    (side P o).Hom (fold o Γ) (fold o Δ) :=
  match o with
  | .conj => ofTerm w.product
  | .disj => ofTerm w.coproduct

theorem sideArrow_get (o : Op) {Γ Δ : List (NormalForm P)} (w : Route Γ Δ)
    {A : NormalForm P} (a : At Δ A) :
    (side P o).comp (w.sideArrow o) (component o a) = component o (w.get a) := by
  cases o
  · exact product_get w a
  · exact coproduct_get w a

end Route

end DosenPetric.Reduced.Gentzen
