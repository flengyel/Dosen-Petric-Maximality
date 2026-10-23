module

public import DosenPetric.GentzenCopiesPositions
public import DosenPetric.GentzenExchangePositions
public import DosenPetric.GentzenAnalysisMacros

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- A derived script of unary structural Gentzen rules, with no leaves or cuts. -/
inductive Rewire (P : Type u) : List (NormalForm P) → List (NormalForm P) → Type u where
  | identity (Γ) : Rewire P Γ Γ
  | seq {Γ Δ Θ} : Rewire P Γ Δ → Rewire P Δ Θ → Rewire P Γ Θ
  | exchange (Γ X Y Θ) : Rewire P (Γ ++ Y ++ X ++ Θ) (Γ ++ X ++ Y ++ Θ)
  | contract (C gs Θ) : 2 ≤ gs.length → Rewire P (gaps gs ++ C :: Θ) (repeated C gs ++ Θ)
  | reindex {Γ Δ Γ' Δ'} : Γ = Γ' → Δ = Δ' → Rewire P Γ Δ → Rewire P Γ' Δ'

namespace Rewire

def arrow (o : Op) : {Γ Δ : List (NormalForm P)} → Rewire P Γ Δ → (side P o).Hom (fold o Γ) (fold o Δ)
  | _, _, .identity _ => (side P o).id _
  | _, _, .seq p q => (side P o).comp (p.arrow o) (q.arrow o)
  | _, _, .exchange Γ X Y Θ => exchangeBack o Γ X Y Θ
  | _, _, .contract C gs Θ _ => (copies C gs Θ).sideArrow o
  | _, _, .reindex hΓ hΔ p => hΓ ▸ hΔ ▸ p.arrow o

def get : {Γ Δ : List (NormalForm P)} → Rewire P Γ Δ → {A : NormalForm P} → At Δ A → At Γ A
  | _, _, .identity _, _, a => a
  | _, _, .seq p q, _, a => p.get (q.get a)
  | _, _, .exchange Γ X Y Θ, _, a => a.swapBlocks Γ X Y Θ
  | _, _, .contract C gs Θ _, _, a => (copies C gs Θ).get a
  | _, _, .reindex hΓ hΔ p, _, a => (p.get (a.cast hΔ.symm)).cast hΓ

theorem arrow_component (o : Op) {Γ Δ : List (NormalForm P)} (p : Rewire P Γ Δ)
    {A : NormalForm P} (a : At Δ A) :
    (side P o).comp (p.arrow o) (component o a) = component o (p.get a) := by
  induction p with
  | identity => exact (side P o).id_comp _
  | seq p q ih ih' => rw [arrow, (side P o).assoc, ih', ih]; rfl
  | exchange => exact exchangeBack_component ..
  | contract => exact Route.sideArrow_get ..
  | reindex hΓ hΔ p ih => cases hΓ; cases hΔ; exact ih a

def left {Γ Δ : List (NormalForm P)} (p : Rewire P Γ Δ) {Λ : List (NormalForm P)}
    (f : G P Δ Λ) : G P Γ Λ :=
  match p with
  | .identity _ => f
  | .seq p q => p.left (q.left f)
  | .exchange Γ X Y Θ => .exchangeL Γ X Y Θ Λ f
  | .contract C gs Θ hn => .contractL C gs Θ Λ hn f
  | .reindex hΓ hΔ p => (p.left (f.reindex hΔ.symm rfl)).reindex hΓ rfl

def right {Γ Δ : List (NormalForm P)} (p : Rewire P Γ Δ) {Λ : List (NormalForm P)}
    (f : G P Λ Δ) : G P Λ Γ :=
  match p with
  | .identity _ => f
  | .seq p q => p.right (q.right f)
  | .exchange Γ X Y Θ => .exchangeR Λ Γ X Y Θ f
  | .contract C gs Θ hn => .contractR Λ C gs Θ hn f
  | .reindex hΓ hΔ p => (p.right (f.reindex rfl hΔ.symm)).reindex rfl hΓ

theorem left_atomized {Γ Δ Λ : List (NormalForm P)} (p : Rewire P Γ Δ) (f : G P Δ Λ) :
    (p.left f).Atomized ↔ f.Atomized := by
  induction p with
  | identity => rfl
  | seq p q ih ih' => exact (ih _).trans (ih' _)
  | exchange => rfl
  | contract => rfl
  | reindex hΓ hΔ p ih => cases hΓ; cases hΔ; exact ih f

theorem right_atomized {Γ Δ Λ : List (NormalForm P)} (p : Rewire P Γ Δ) (f : G P Λ Δ) :
    (p.right f).Atomized ↔ f.Atomized := by
  induction p with
  | identity => rfl
  | seq p q ih ih' => exact (ih _).trans (ih' _)
  | exchange => rfl
  | contract => rfl
  | reindex hΓ hΔ p ih => cases hΓ; cases hΔ; exact ih f

theorem left_count {Γ Δ Λ : List (NormalForm P)} (p : Rewire P Γ Δ) (f : G P Δ Λ) :
    (p.left f).cutCount = f.cutCount := by
  induction p with
  | identity => rfl
  | seq p q ih ih' => exact (ih _).trans (ih' _)
  | exchange => rfl
  | contract => rfl
  | reindex hΓ hΔ p ih => cases hΓ; cases hΔ; exact ih f

theorem right_count {Γ Δ Λ : List (NormalForm P)} (p : Rewire P Γ Δ) (f : G P Λ Δ) :
    (p.right f).cutCount = f.cutCount := by
  induction p with
  | identity => rfl
  | seq p q ih ih' => exact (ih _).trans (ih' _)
  | exchange => rfl
  | contract => rfl
  | reindex hΓ hΔ p ih => cases hΓ; cases hΔ; exact ih f

theorem left_denote {Γ Δ Λ : List (NormalForm P)} (p : Rewire P Γ Δ) (f : G P Δ Λ) :
    ofTerm (p.left f).denote = comp (p.arrow .conj) (ofTerm f.denote) := by
  induction p with
  | identity => exact (Laws.id_comp _).symm
  | seq p q ih ih' => rw [left, ih, ih']; exact (Laws.assoc ..).symm
  | exchange => rfl
  | contract => rfl
  | reindex hΓ hΔ p ih => cases hΓ; cases hΔ; exact ih f

theorem right_denote {Γ Δ Λ : List (NormalForm P)} (p : Rewire P Γ Δ) (f : G P Λ Δ) :
    ofTerm (p.right f).denote = comp (ofTerm f.denote) (p.arrow .disj) := by
  induction p with
  | identity => exact (Laws.comp_id _).symm
  | seq p q ih ih' => rw [right, ih, ih']; exact Laws.assoc ..
  | exchange => rfl
  | contract => rfl
  | reindex hΓ hΔ p ih => cases hΓ; cases hΔ; exact ih f

theorem get_index_reindex {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (p : Rewire P Γ Δ) {A : NormalForm P} (a : At Δ' A) :
    ((p.reindex hΓ hΔ).get a).index = (p.get (a.cast hΔ.symm)).index := by
  cases hΓ; cases hΔ; rfl

end Rewire
end DosenPetric.Reduced.Gentzen
