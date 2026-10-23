module

public import DosenPetric.GentzenDisjunction

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace Route

def get {Γ Δ : List (NormalForm P)} {A : NormalForm P} : Route Γ Δ → At Δ A → At Γ A
  | .cons a _, .here _ _ => a
  | .cons _ w, .there b => get w b

theorem product_get {Γ Δ : List (NormalForm P)} {A : NormalForm P}
    (w : Route Γ Δ) (a : At Δ A) :
    comp (ofTerm w.product) (ofTerm a.projection) = ofTerm (w.get a).projection := by
  induction a with
  | here A Δ => cases w with | cons b w => exact (conjDiagonal P).pair_fst (ofTerm b.projection) (ofTerm w.product)
  | there a ih =>
    cases w with | cons b w =>
    change comp (pair (ofTerm b.projection) (ofTerm w.product))
      (comp (snd _ _) (ofTerm a.projection)) = _
    rw [← Laws.assoc]
    have h : comp (pair (ofTerm b.projection) (ofTerm w.product)) (snd _ _) = ofTerm w.product :=
      (conjDiagonal P).pair_snd (ofTerm b.projection) (ofTerm w.product)
    rw [h]
    exact ih w

theorem coproduct_get {Γ Δ : List (NormalForm P)} {A : NormalForm P}
    (w : Route Γ Δ) (a : At Δ A) :
    comp (ofTerm a.injection) (ofTerm w.coproduct) = ofTerm (w.get a).injection := by
  induction a with
  | here A Δ => cases w with | cons b w => exact (disjDiagonal P).pair_fst (ofTerm b.injection) (ofTerm w.coproduct)
  | there a ih =>
    cases w with | cons b w =>
    change comp (comp (ofTerm a.injection) (inr _ _))
      (copair (ofTerm b.injection) (ofTerm w.coproduct)) = _
    rw [Laws.assoc]
    have h : comp (inr _ _) (copair (ofTerm b.injection) (ofTerm w.coproduct)) = ofTerm w.coproduct :=
      (disjDiagonal P).pair_snd (ofTerm b.injection) (ofTerm w.coproduct)
    rw [h]
    exact ih w

end Route

theorem product_positions {X : NormalForm P} {Γ : List (NormalForm P)}
    (f g : Hom X (ante Γ))
    (h : ∀ {A} (a : At Γ A), comp f (ofTerm a.projection) = comp g (ofTerm a.projection)) : f = g := by
  induction Γ with
  | nil => exact ((conjDiagonal P).toUnit_unique f).trans ((conjDiagonal P).toUnit_unique g).symm
  | cons A Γ ih =>
    apply conj_ext
    · exact h (.here A Γ)
    · apply ih
      intro B a
      have hh := h (.there a)
      change comp f (comp (snd A (ante Γ)) (ofTerm a.projection)) =
        comp g (comp (snd A (ante Γ)) (ofTerm a.projection)) at hh
      simpa only [Laws.assoc] using hh

theorem coproduct_positions {X : NormalForm P} {Γ : List (NormalForm P)}
    (f g : Hom (succ Γ) X)
    (h : ∀ {A} (a : At Γ A), comp (ofTerm a.injection) f = comp (ofTerm a.injection) g) : f = g := by
  induction Γ with
  | nil => exact ((disjDiagonal P).toUnit_unique f).trans ((disjDiagonal P).toUnit_unique g).symm
  | cons A Γ ih =>
    apply disj_ext
    · exact h (.here A Γ)
    · apply ih
      intro B a
      have hh := h (.there a)
      change comp (comp (ofTerm a.injection) (inr A (succ Γ))) f =
        comp (comp (ofTerm a.injection) (inr A (succ Γ))) g at hh
      simpa only [Laws.assoc] using hh

theorem input_in {A B : NormalForm P} (g : G P [A] [B]) :
    comp (rightIn .conj A) (ofTerm g.denote) = comp (decode g.denote) (rightIn .disj B) := by
  simp only [decode, Laws.assoc]
  rw [Laws.rightOut_In, Laws.comp_id]

theorem output_out {A B : NormalForm P} (g : G P [A] [B]) :
    comp (ofTerm g.denote) (rightOut .disj B) = comp (rightOut .conj A) (decode g.denote) := by
  simp only [decode, ← Laws.assoc]
  rw [Laws.rightOut_In, Laws.id_comp]

theorem denote_value {A B : NormalForm P} (g : G P [A] [B]) :
    ofTerm g.denote = comp (rightOut .conj A) (comp (decode g.denote) (rightIn .disj B)) := by
  rw [← Laws.assoc, ← output_out, Laws.assoc, Laws.rightOut_In, Laws.comp_id]

end DosenPetric.Reduced.Gentzen
