module

public import DosenPetric.GentzenLogicalDeletionTail

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace G

theorem reindex_congr {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    {f g : G P Γ Δ} (he : ofTerm f.denote = ofTerm g.denote) :
    ofTerm (f.reindex hΓ hΔ).denote = ofTerm (g.reindex hΓ hΔ).denote := by
  cases hΓ; cases hΔ; exact he

theorem reindex_left_cancel_denote {Γ Γ' Δ : List (NormalForm P)} (hΓ : Γ = Γ')
    (f : G P Γ Δ) (g : G P Γ' Δ) (he : ofTerm (f.reindex hΓ rfl).denote = ofTerm g.denote) :
    ofTerm f.denote = ofTerm (g.reindex hΓ.symm rfl).denote := by cases hΓ; exact he

theorem reindex_right_cancel_denote {Γ Δ Δ' : List (NormalForm P)} (hΔ : Δ = Δ')
    (f : G P Γ Δ) (g : G P Γ Δ') (he : ofTerm (f.reindex rfl hΔ).denote = ofTerm g.denote) :
    ofTerm f.denote = ofTerm (g.reindex rfl hΔ.symm).denote := by cases hΔ; exact he

end G
namespace PositionalCut

/-- Canonicalize only the two residual list equalities; selected proof nodes are unchanged. -/
theorem reindex_residues {Γ Δ Θ Λ D T : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hD : x.erase = D) (hT : y.erase = T) :
    (cut f x g y).reindex (congrArg (fun xs => xs ++ Γ) hT) (congrArg (fun xs => Λ ++ xs) hD) =
      G.cut ((x.toHead.reindex (congrArg (List.cons C) hD) rfl).right f)
        ((y.toHead.reindex (congrArg (List.cons C) hT) rfl).left g) := by
  cases hD; cases hT; rfl

end PositionalCut
namespace SuffixedLogical

/-- The actual conjunction-left rule before a fixed input suffix. -/
def conjL (F U K Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P ((F ++ A :: B :: U) ++ K) Δ) : G P ((F ++ .conj A B :: U) ++ K) Δ :=
  (ExchangeScript.appendAssoc F (.conj A B :: U) K).inverse.left
    (G.conjL F (U ++ K) Δ A B ((ExchangeScript.appendAssoc F (A :: B :: U) K).left f))

theorem conjL_denote (F U K Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P ((F ++ A :: B :: U) ++ K) Δ) :
    ofTerm (conjL F U K Δ A B f).denote =
      comp (suffixLogicalSide .conj F U K A B) (ofTerm f.denote) := by
  unfold conjL
  rw [ExchangeScript.left_denote,G.denote_conjL,ExchangeScript.left_denote,conjLeft_compare]
  change comp _ (comp (logicalSide .conj F (U ++ K) A B) (comp _ (ofTerm f.denote))) = _
  dsimp only [suffixLogicalSide,side,category]
  simp only [Laws.assoc]

theorem conjL_count (F U K Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P ((F ++ A :: B :: U) ++ K) Δ) : (conjL F U K Δ A B f).cutCount = f.cutCount := by
  simp only [conjL,ExchangeScript.left_count,G.cutCount]

theorem conjL_atomized (F U K Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P ((F ++ A :: B :: U) ++ K) Δ) : (conjL F U K Δ A B f).Atomized ↔ f.Atomized := by
  simp only [conjL,ExchangeScript.left_atomized,G.Atomized]

end SuffixedLogical
end DosenPetric.Reduced.Gentzen
