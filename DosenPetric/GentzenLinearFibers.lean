module

public import DosenPetric.GentzenFiberOrder

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace TraceRoute

theorem ext {Γ Δ : List (NormalForm P)} (w v : TraceRoute Γ Δ)
    (h : ∀ {A} (a : At Δ A), w.get a = v.get a) : w = v := by
  induction w with
  | nil => cases v; rfl
  | cons a w ih =>
    cases v with
    | cons b v =>
      have hh := h (.here _ _)
      change a = b at hh
      cases hh
      exact congrArg (cons a) (ih v (fun a => h a.there))

theorem fiber_inverse {Γ Δ : List (NormalForm P)} {C : NormalForm P}
    (w : TraceRoute Γ Δ) (x : At Γ C) (inv : Option (At Δ C))
    (h : ∀ y, w.get y = some x ↔ inv = some y) : fiber x w = inv.toList := by
  cases inv with
  | none => exact fiber_empty w x (fun y hy => by have hh := (h y).mp hy; cases hh)
  | some y =>
    apply fiber_single w x y
    intro z
    exact (h z).trans (by simp [eq_comm])

theorem fiber_identity (Γ : List (NormalForm P)) {C : NormalForm P} (x : At Γ C) :
    (ofMap Γ Γ (fun a => some a)).fiber x = [x] := by
  apply fiber_single
  intro a
  simp only [get_ofMap,Option.some.injEq]

theorem fiber_fixed (Γ X Y Θ : List (NormalForm P)) {C : NormalForm P}
    (x : At (Γ ++ (Y ++ Θ)) C) :
    (ofMap _ _ (At.fixed Γ X Y Θ)).fiber x = (At.fixed Γ Y X Θ x).toList := by
  apply fiber_inverse
  intro y
  rw [get_ofMap]
  exact At.fixed_reverse Γ X Y Θ y x

def before (Γ Θ : List (NormalForm P)) : TraceRoute (Γ ++ Θ) Γ :=
  ofMap _ _ (fun a => some (a.before Θ))

def shift (Γ Θ : List (NormalForm P)) : TraceRoute (Γ ++ Θ) Θ :=
  ofMap _ _ (fun a => some (At.shift Γ a))

theorem fiber_before (Γ Θ : List (NormalForm P)) {C : NormalForm P} (x : At (Γ ++ Θ) C) :
    (before Γ Θ).fiber x = match At.splitAppend Γ Θ x with | .inl a => [a] | .inr _ => [] := by
  cases At.cases_append Γ Θ x with
  | inl hx =>
    obtain ⟨x,rfl⟩ := hx
    rw [At.splitAppend_before]
    apply fiber_single
    intro y
    rw [before,get_ofMap,Option.some.injEq]
    constructor
    · intro h
      apply At.index_injective
      have hi := congrArg At.index h
      simpa only [At.index_before] using hi
    · intro h; cases h; rfl
  | inr hx =>
    obtain ⟨x,rfl⟩ := hx
    rw [At.splitAppend_shift]
    apply fiber_empty
    intro y h
    rw [before,get_ofMap,Option.some.injEq] at h
    have hi := congrArg At.index h
    have hl := y.index_lt
    simp only [At.index_before,At.index_shift] at hi
    omega

theorem fiber_shift (Γ Θ : List (NormalForm P)) {C : NormalForm P} (x : At (Γ ++ Θ) C) :
    (shift Γ Θ).fiber x = match At.splitAppend Γ Θ x with | .inl _ => [] | .inr a => [a] := by
  cases At.cases_append Γ Θ x with
  | inl hx =>
    obtain ⟨x,rfl⟩ := hx
    rw [At.splitAppend_before]
    apply fiber_empty
    intro y h
    rw [shift,get_ofMap,Option.some.injEq] at h
    have hi := congrArg At.index h
    have hl := x.index_lt
    simp only [At.index_before,At.index_shift] at hi
    omega
  | inr hx =>
    obtain ⟨x,rfl⟩ := hx
    rw [At.splitAppend_shift]
    apply fiber_single
    intro y
    rw [shift,get_ofMap,Option.some.injEq]
    constructor
    · intro h
      apply At.index_injective
      have hi := congrArg At.index h
      simp only [At.index_shift] at hi
      omega
    · intro h; cases h; rfl

/-- Remove the upper principal formula, and insert the new lower principal
    formula without identifying their components. -/
def wrap {Γ Δ : List (NormalForm P)} (A B : NormalForm P) (w : TraceRoute Γ Δ) :
    TraceRoute (A :: Γ) (B :: Δ) :=
  .cons none (ofMap _ _ (fun a => (w.get a).map At.there))

theorem fiber_wrap_here {Γ Δ : List (NormalForm P)} (A B : NormalForm P) (w : TraceRoute Γ Δ) :
    (wrap A B w).fiber (.here A Γ) = [] := by
  apply fiber_empty
  intro y h
  cases y with
  | here => cases h
  | there y =>
    simp only [wrap,get,get_ofMap] at h
    cases hh : w.get y <;> simp only [hh,Option.map_none,Option.map_some] at h <;> cases h

theorem fiber_wrap_there {Γ Δ : List (NormalForm P)} (A B : NormalForm P) (w : TraceRoute Γ Δ)
    {C : NormalForm P} (x : At Γ C) :
    (wrap A B w).fiber x.there = (w.fiber x).map At.there := by
  apply At.ordered_ext _ _ (fiber_ordered _ _) (At.ordered_there (fiber_ordered w x))
  intro y
  rw [fiber_correct]
  cases y with
  | here => simp only [wrap,get,List.mem_map]; constructor <;> intro h
            · cases h
            · obtain ⟨_,_,h⟩ := h; cases h
  | there y =>
    rw [mem_there,fiber_correct]
    simp only [wrap,get,get_ofMap]
    cases w.get y <;> simp

theorem fiber_skip {Γ Δ : List (NormalForm P)} (B : NormalForm P) (w : TraceRoute Γ Δ)
    {C : NormalForm P} (x : At Γ C) :
    (TraceRoute.cons (A := B) none w).fiber x = (w.fiber x).map At.there := rfl

end TraceRoute

namespace At

theorem fixed_single_none (Γ Θ Y : List (NormalForm P)) (A : NormalForm P)
    {C : NormalForm P} (x : At (Γ ++ A :: Θ) C) :
    fixed Γ [A] Y Θ x = none ↔ x.index = Γ.length := by
  cases cases_append Γ (A :: Θ) x with
  | inl hx =>
    obtain ⟨x,rfl⟩ := hx
    change fixed Γ [A] Y Θ (x.before ([A] ++ Θ)) = none ↔ _
    rw [fixed_before]
    have hl := x.index_lt
    simp only [index_before]
    constructor
    · intro h; cases h
    · intro h; omega
  | inr hx =>
    obtain ⟨x,rfl⟩ := hx
    cases x with
    | here =>
      have hf := fixed_middle Γ [A] Y Θ (.here A [])
      constructor
      · intro _; simp only [index_shift,index,Nat.add_zero]
      · intro _; simpa only [before,List.nil_append] using hf
    | there x =>
      have hf := fixed_tail Γ [A] Y Θ x
      change fixed Γ [A] Y Θ (At.shift Γ (At.shift [A] x)) = none ↔ _
      rw [hf]
      simp only [index_shift,index]
      constructor
      · intro h; cases h
      · intro h; omega

end At
end DosenPetric.Reduced.Gentzen
