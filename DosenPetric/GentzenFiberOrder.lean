module

public import DosenPetric.GentzenTraceFibers

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace At

def Ordered {Γ : List (NormalForm P)} {C : NormalForm P} (xs : List (At Γ C)) : Prop :=
  xs.Pairwise (fun a b => a.index < b.index)

theorem ordered_there {Γ : List (NormalForm P)} {A C : NormalForm P}
    {xs : List (At Γ C)} (h : Ordered xs) : Ordered (xs.map (@At.there P C A Γ)) := by
  apply h.map
  intro a b hab
  simp only [index]
  omega

theorem ordered_ext {Γ : List (NormalForm P)} {C : NormalForm P}
    (xs ys : List (At Γ C)) (hx : Ordered xs) (hy : Ordered ys)
    (hm : ∀ a, a ∈ xs ↔ a ∈ ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons a ys => have hh := (hm a).mpr List.mem_cons_self; cases hh
  | cons a xs ih =>
    cases ys with
    | nil => have hh := (hm a).mp List.mem_cons_self; cases hh
    | cons b ys =>
      have hab : a = b := by
        cases List.mem_cons.mp ((hm a).mp List.mem_cons_self) with
        | inl h => exact h
        | inr ha =>
          cases List.mem_cons.mp ((hm b).mpr List.mem_cons_self) with
          | inl h => exact h.symm
          | inr hb =>
            have h₁ := List.rel_of_pairwise_cons hx hb
            have h₂ := List.rel_of_pairwise_cons hy ha
            omega
      cases hab
      apply congrArg (List.cons a)
      apply ih _ hx.of_cons hy.of_cons
      intro z
      constructor
      · intro hz
        cases List.mem_cons.mp ((hm z).mp (List.mem_cons_of_mem _ hz)) with
        | inr h => exact h
        | inl h =>
          have hh := List.rel_of_pairwise_cons hx hz
          cases h
          omega
      · intro hz
        cases List.mem_cons.mp ((hm z).mpr (List.mem_cons_of_mem _ hz)) with
        | inr h => exact h
        | inl h =>
          have hh := List.rel_of_pairwise_cons hy hz
          cases h
          omega

end At

namespace TraceRoute

theorem fiber_ordered {Γ Δ : List (NormalForm P)} {C : NormalForm P}
    (w : TraceRoute Γ Δ) (x : At Γ C) : At.Ordered (fiber x w) := by
  induction w with
  | nil => exact .nil
  | @cons A Δ a w ih =>
    cases a with
    | none => exact At.ordered_there ih
    | some a =>
      cases h : At.compare x a with
      | same =>
        simp only [fiber,h]
        apply List.Pairwise.cons
        · intro b hb
          obtain ⟨b,_,rfl⟩ := List.mem_map.mp hb
          simp only [At.index]
          omega
        · exact At.ordered_there ih
      | apart => simpa only [fiber,h] using At.ordered_there (A := A) ih

theorem fiber_ext {Γ Θ Δ : List (NormalForm P)} {C : NormalForm P}
    (w : TraceRoute Γ Δ) (v : TraceRoute Θ Δ) (x : At Γ C) (y : At Θ C)
    (h : ∀ a, w.get a = some x ↔ v.get a = some y) : fiber x w = fiber y v :=
  At.ordered_ext _ _ (fiber_ordered w x) (fiber_ordered v y)
    (fun a => (fiber_correct w x a).trans ((h a).trans (fiber_correct v y a).symm))

theorem fiber_empty {Γ Δ : List (NormalForm P)} {C : NormalForm P}
    (w : TraceRoute Γ Δ) (x : At Γ C) (h : ∀ a, w.get a ≠ some x) : fiber x w = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro a ha
  exact h a ((fiber_correct w x a).mp ha)

theorem fiber_single {Γ Δ : List (NormalForm P)} {C : NormalForm P}
    (w : TraceRoute Γ Δ) (x : At Γ C) (y : At Δ C)
    (h : ∀ a, w.get a = some x ↔ a = y) : fiber x w = [y] := by
  apply At.ordered_ext _ _ (fiber_ordered w x) (.cons (by intro _ h; cases h) .nil)
  intro a
  exact (fiber_correct w x a).trans ((h a).trans (by simp))

end TraceRoute
end DosenPetric.Reduced.Gentzen
