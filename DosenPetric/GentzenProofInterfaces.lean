module

public import DosenPetric.GentzenOccurrences

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- The atoms used for source thinning atomization, including both constants. -/
def AtomicFormula : NormalForm P → Prop
  | .lit _ | .top | .bot => True
  | .conj _ _ | .disj _ _ => False

namespace G

def Atomized : {Γ Δ : List (NormalForm P)} → G P Γ Δ → Prop
  | _, _, .identity _ | _, _, .zero _ | _, _, .topI | _, _, .botE => True
  | _, _, .exchangeL _ _ _ _ _ f | _, _, .exchangeR _ _ _ _ _ f
  | _, _, .contractL _ _ _ _ _ f | _, _, .contractR _ _ _ _ _ f
  | _, _, .conjL _ _ _ _ _ f | _, _, .disjR _ _ _ _ _ f => f.Atomized
  | _, _, .thinL _ _ _ A f | _, _, .thinR _ _ _ A f => AtomicFormula A ∧ f.Atomized
  | _, _, .conjR f g | _, _, .disjL f g | _, _, .mix f g | _, _, .cut f g => f.Atomized ∧ g.Atomized

/-- Topmost cut records cut-free premises, without asserting any reduction. -/
def Topmost {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) : Prop := f.CutFree ∧ g.CutFree

theorem conjR_cutFree {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) :
    (G.conjR f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [CutFree, cutCount, Nat.add_eq_zero_iff]

theorem disjL_cutFree {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) :
    (G.disjL f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [CutFree, cutCount, Nat.add_eq_zero_iff]

theorem mix_cutFree {Γ Θ Δ Λ : List (NormalForm P)}
    (f : G P Γ Δ) (g : G P Θ Λ) : (G.mix f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [CutFree, cutCount, Nat.add_eq_zero_iff]

end G
end DosenPetric.Reduced.Gentzen
