module

public import DosenPetric.GentzenContexts

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- A positional occurrence of a whole formula in a context, not label membership. -/
inductive At : List (NormalForm P) → NormalForm P → Type u where
  | here (A Γ) : At (A :: Γ) A
  | there {A B Γ} : At Γ A → At (B :: Γ) A

namespace At

def shift (Γ : List (NormalForm P)) {Δ A} (a : At Δ A) : At (Γ ++ Δ) A :=
  match Γ with
  | [] => a
  | _ :: Γ => .there (shift Γ a)

def before {Γ A} (a : At Γ A) (Δ : List (NormalForm P)) : At (Γ ++ Δ) A :=
  match a with
  | .here A Γ => .here A (Γ ++ Δ)
  | .there a => .there (before a Δ)

def projection {Γ A} : At (P := P) Γ A → Term P (ante Γ) A
  | .here A Γ => .fst A (ante Γ)
  | .there a => .comp (.snd _ _) a.projection

def injection {Γ A} : At (P := P) Γ A → Term P A (succ Γ)
  | .here A Γ => .inl A (succ Γ)
  | .there a => .comp a.injection (.inr _ _)

theorem projection_positive {Γ A} (a : At (P := P) Γ A) : a.projection.Positive := by
  induction a with
  | here => exact .fst ..
  | there _ ih => exact .comp (.snd ..) ih

theorem injection_positive {Γ A} (a : At (P := P) Γ A) : a.injection.Positive := by
  induction a with
  | here => exact .inl ..
  | there _ ih => exact .comp ih (.inr ..)
end At

/-- Each output formula chooses one input position of exactly the same type. -/
inductive Route (Γ : List (NormalForm P)) : List (NormalForm P) → Type u where
  | nil : Route Γ []
  | cons {A Δ} : At Γ A → Route Γ Δ → Route Γ (A :: Δ)

namespace Route

def map {Γ Θ Δ} (f : {A : NormalForm P} → At Γ A → At Θ A) : Route Γ Δ → Route Θ Δ
  | .nil => .nil
  | .cons a w => .cons (f a) (map f w)

def identity : (Γ : List (NormalForm P)) → Route Γ Γ
  | [] => .nil
  | A :: Γ => .cons (.here A Γ) (map At.there (identity Γ))

def append {Γ Δ Θ : List (NormalForm P)} : Route Γ Δ → Route Γ Θ → Route Γ (Δ ++ Θ)
  | .nil, w => w
  | .cons a v, w => .cons a (append v w)

def product {Γ Δ} : Route (P := P) Γ Δ → Term P (ante Γ) (ante Δ)
  | .nil => .toTop _
  | .cons a w => .pair a.projection w.product

def coproduct {Γ Δ} : Route (P := P) Γ Δ → Term P (succ Δ) (succ Γ)
  | .nil => .fromBot _
  | .cons a w => .copair a.injection w.coproduct

theorem product_positive {Γ Δ} (w : Route (P := P) Γ Δ) : w.product.Positive := by
  induction w with
  | nil => exact .comp (.rightIn ..) (.snd ..)
  | cons a w ih => exact .comp (.diag _) (.tensor _ a.projection_positive ih)

theorem coproduct_positive {Γ Δ} (w : Route (P := P) Γ Δ) : w.coproduct.Positive := by
  induction w with
  | nil => exact .comp (.inr ..) (.rightOut ..)
  | cons a w ih => exact .comp (.tensor _ a.injection_positive ih) (.codiag _)

/-- Inserted formula is ignored; all other positions keep their individual tags. -/
def thin (Γ Δ : List (NormalForm P)) (A : NormalForm P) : Route (Γ ++ A :: Δ) (Γ ++ Δ) :=
  match Γ with
  | [] => map At.there (identity Δ)
  | B :: Γ => .cons (.here B _) (map At.there (thin Γ Δ A))
end Route

/-- Concatenate fixed gaps by structural recursion, retaining their positions. -/
@[reducible] def gaps : List (List (NormalForm P)) → List (NormalForm P)
  | [] => []
  | Γ :: gs => Γ ++ gaps gs

theorem gaps_eq_flatten (gs : List (List (NormalForm P))) : gaps gs = gs.flatten := by
  induction gs with
  | nil => rfl
  | cons Γ gs ih => exact congrArg (fun Δ => Γ ++ Δ) ih

/-- One selected copy after each gap. Equal formulas elsewhere stay fixed. -/
@[reducible] def repeated (C : NormalForm P) : List (List (NormalForm P)) → List (NormalForm P)
  | [] => []
  | Γ :: gs => Γ ++ C :: repeated C gs

def copies (C : NormalForm P) : (gs : List (List (NormalForm P))) → (Δ : List (NormalForm P)) →
    Route (gaps gs ++ C :: Δ) (repeated C gs ++ Δ)
  | [], Δ => Route.map At.there (Route.identity Δ)
  | Γ :: gs, Δ => by
    have h : Route (Γ ++ (gaps gs ++ C :: Δ)) (Γ ++ C :: (repeated C gs ++ Δ)) :=
      Route.append (Route.map (fun a => a.before _) (Route.identity Γ))
        (.cons (At.shift Γ (At.shift (gaps gs) (.here C Δ)))
          (Route.map (fun a => At.shift Γ a) (copies C gs Δ)))
    simpa only [gaps, repeated, List.append_assoc, List.cons_append] using h

/-- Raw structural interpretation equations for positional routing. -/
theorem product_cons {Γ Δ A} (a : At (P := P) Γ A) (w : Route Γ Δ) :
    ofTerm (Route.cons a w).product = pair (ofTerm a.projection) (ofTerm w.product) := rfl

theorem coproduct_cons {Γ Δ A} (a : At (P := P) Γ A) (w : Route Γ Δ) :
    ofTerm (Route.cons a w).coproduct = copair (ofTerm a.injection) (ofTerm w.coproduct) := rfl

end DosenPetric.Reduced.Gentzen
