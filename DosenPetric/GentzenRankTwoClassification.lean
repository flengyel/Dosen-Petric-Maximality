module

public import DosenPetric.GentzenAtomicCutElimination

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PositionalCut

/-- The only non-atomic principal pairs at selected rank two. -/
inductive PrincipalPair : {Γ Δ Θ Λ : List (NormalForm P)} → {C : NormalForm P} →
    (f : G P Γ Δ) → At Δ C → (g : G P Θ Λ) → At Θ C → Prop where
  | conj {Γ Θ Δ Λ F U V A B} (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ))
      (h : G P (F ++ A :: B :: U) V) :
      PrincipalPair (G.conjR f g) (.here (.conj A B) (Δ ++ Λ))
        (G.conjL F U V A B h) (At.shift F (.here (.conj A B) U))
  | disj {Γ Δ Λ F U V W A B} (f : G P Γ (Δ ++ A :: B :: Λ))
      (g : G P (A :: F) V) (h : G P (B :: U) W) :
      PrincipalPair (G.disjR Γ Δ Λ A B f) (At.shift Δ (.here (.disj A B) Λ))
        (G.disjL g h) (.here (.disj A B) (F ++ U))

/-- Complete least-rank classification, with the atomic branch already eliminated. -/
theorem rank_two_classification {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hf : f.CutFree) (hg : g.CutFree) (af : f.Atomized) (ag : g.Atomized)
    (hr : rank f x g y = 2) :
    (AtomicFormula C ∧ Eliminated f x g y) ∨ PrincipalPair f x g y := by
  have hx := rightLeaf_complete f af x ((rank_two_iff_leaves f x g y).mp hr).1
  have hy := leftLeaf_complete g ag y ((rank_two_iff_leaves f x g y).mp hr).2
  cases C with
  | lit l => exact .inl ⟨True.intro, atomic_rank_two f x g y hf hg af ag True.intro hr⟩
  | top => exact .inl ⟨True.intro, atomic_rank_two f x g y hf hg af ag True.intro hr⟩
  | bot => exact .inl ⟨True.intro, atomic_rank_two f x g y hf hg af ag True.intro hr⟩
  | conj A B =>
    right
    cases hx with
    | thin _ _ _ _ _ ha => cases ha
    | conj f g =>
      cases hy with
      | thin _ _ _ _ _ ha => cases ha
      | conj _ _ _ _ _ h => exact .conj f g h
  | disj A B =>
    right
    cases hx with
    | thin _ _ _ _ _ ha => cases ha
    | disj _ _ _ _ _ f =>
      cases hy with
      | thin _ _ _ _ _ ha => cases ha
      | disj g h => exact .disj f g h

end PositionalCut
end DosenPetric.Reduced.Gentzen
