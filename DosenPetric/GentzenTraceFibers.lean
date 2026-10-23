module

public import DosenPetric.GentzenTracePositions

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace At

/-- Compare positions in one context, even when their formula indices differ.
    Equality is determined by the positions, never by formula comparison. -/
inductive Comparison : {Γ : List (NormalForm P)} → {A B : NormalForm P} →
    At Γ A → At Γ B → Type u where
  | same {Γ A} (a : At Γ A) : Comparison a a
  | apart {Γ A B} {a : At Γ A} {b : At Γ B} : a.index ≠ b.index → Comparison a b

def compare {Γ : List (NormalForm P)} {A B : NormalForm P}
    (a : At Γ A) (b : At Γ B) : Comparison a b :=
  match a,b with
  | .here _ _, .here _ _ => .same _
  | .here _ _, .there b => .apart (by simp only [index]; omega)
  | .there a, .here _ _ => .apart (by simp only [index]; omega)
  | .there a, .there b => match compare a b with
    | .same _ => .same _
    | .apart h => .apart (by simp only [index]; omega)

end At

/-- A partial, formula-preserving map from upper to lower sequent positions. -/
inductive TraceRoute (Γ : List (NormalForm P)) : List (NormalForm P) → Type u where
  | nil : TraceRoute Γ []
  | cons {A Δ} : Option (At Γ A) → TraceRoute Γ Δ → TraceRoute Γ (A :: Δ)

namespace TraceRoute

def get {Γ Δ : List (NormalForm P)} : TraceRoute Γ Δ → {A : NormalForm P} → At Δ A → Option (At Γ A)
  | .cons a _, _, .here _ _ => a
  | .cons _ w, _, .there a => w.get a

def ofMap (Γ Δ : List (NormalForm P))
    (f : {A : NormalForm P} → At Δ A → Option (At Γ A)) : TraceRoute Γ Δ :=
  match Δ with
  | [] => .nil
  | A :: Δ => .cons (f (.here A Δ)) (ofMap Γ Δ (fun a => f a.there))

theorem get_ofMap (Γ Δ : List (NormalForm P))
    (f : {A : NormalForm P} → At Δ A → Option (At Γ A))
    {A : NormalForm P} (a : At Δ A) : (ofMap Γ Δ f).get a = f a := by
  induction a with
  | here => rfl
  | there a ih => exact ih _

def full {Γ Δ : List (NormalForm P)} (w : Route Γ Δ) : TraceRoute Γ Δ :=
  ofMap Γ Δ (fun a => some (w.get a))

theorem get_full {Γ Δ : List (NormalForm P)} (w : Route Γ Δ)
    {A : NormalForm P} (a : At Δ A) : (full w).get a = some (w.get a) := get_ofMap ..

/-- Enumerate every upper preimage of one specified lower position. -/
def fiber {Γ : List (NormalForm P)} {A : NormalForm P} (x : At Γ A) :
    {Δ : List (NormalForm P)} → TraceRoute Γ Δ → List (At Δ A)
  | [], .nil => []
  | _ :: _, .cons none w => (fiber x w).map At.there
  | _ :: Δ, .cons (some a) w => match At.compare x a with
    | .same _ => .here _ Δ :: (fiber x w).map At.there
    | .apart _ => (fiber x w).map At.there

theorem mem_there {Γ : List (NormalForm P)} {A B : NormalForm P}
    (xs : List (At Γ A)) (a : At Γ A) : a.there ∈ xs.map (@At.there P A B Γ) ↔ a ∈ xs := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨b,hb,h⟩; cases h; exact hb
  · intro h; exact ⟨a,h,rfl⟩

theorem here_not_mem_there {Γ : List (NormalForm P)} {A : NormalForm P}
    (xs : List (At Γ A)) : At.here A Γ ∉ xs.map (@At.there P A A Γ) := by
  simp only [List.mem_map]
  rintro ⟨b,_,h⟩; cases h

theorem fiber_correct {Γ Δ : List (NormalForm P)} {A : NormalForm P}
    (w : TraceRoute Γ Δ) (x : At Γ A) (y : At Δ A) :
    y ∈ fiber x w ↔ w.get y = some x := by
  induction w with
  | nil => cases y
  | @cons B Δ a w ih =>
    cases a with
    | none =>
      cases y with
      | here => simp only [fiber, get, List.mem_map]; constructor <;> intro h
                · obtain ⟨_,_,h⟩ := h; cases h
                · cases h
      | there y => exact (mem_there _ y).trans (ih y)
    | some a =>
      cases h : At.compare x a with
      | same =>
        cases y with
        | here => simp [fiber, h, get]
        | there y =>
          simpa [fiber, h, get] using (mem_there (B := A) (fiber x w) y).trans (ih y)
      | apart hn =>
        cases y with
        | here =>
          simp only [fiber, h, List.mem_map, get]
          constructor
          · rintro ⟨_,_,hh⟩; cases hh
          · intro hh; have he := congrArg At.index (Option.some.inj hh); exact False.elim (hn he.symm)
        | there y =>
          simpa only [fiber, h, get] using (mem_there (B := B) (fiber x w) y).trans (ih y)

end TraceRoute
end DosenPetric.Reduced.Gentzen
