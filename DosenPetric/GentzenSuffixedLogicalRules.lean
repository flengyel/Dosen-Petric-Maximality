module

public import DosenPetric.GentzenSuffixLogical

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SuffixedLogical

/-- The actual disjunction-right rule with a fixed output suffix. -/
def disjR (Γ F U K : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ ((F ++ A :: B :: U) ++ K)) : G P Γ ((F ++ .disj A B :: U) ++ K) :=
  (ExchangeScript.appendAssoc F (.disj A B :: U) K).inverse.right
    (G.disjR Γ F (U ++ K) A B ((ExchangeScript.appendAssoc F (A :: B :: U) K).right f))

theorem disjR_denote (Γ F U K : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ ((F ++ A :: B :: U) ++ K)) :
    ofTerm (disjR Γ F U K A B f).denote =
      comp (ofTerm f.denote) (suffixLogicalSide .disj F U K A B) := by
  unfold disjR
  rw [ExchangeScript.right_denote,G.denote_disjR,ExchangeScript.right_denote,disjRight_compare]
  change comp (comp (comp (ofTerm f.denote) _) (logicalSide .disj F (U ++ K) A B)) _ = _
  dsimp only [suffixLogicalSide,side,category,opposite]
  simp only [Laws.assoc]

theorem disjR_count (Γ F U K : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ ((F ++ A :: B :: U) ++ K)) : (disjR Γ F U K A B f).cutCount = f.cutCount := by
  simp only [disjR,ExchangeScript.right_count,G.cutCount]

theorem disjR_atomized (Γ F U K : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ ((F ++ A :: B :: U) ++ K)) :
    (disjR Γ F U K A B f).Atomized ↔ f.Atomized := by
  simp only [disjR,ExchangeScript.right_atomized,G.Atomized]

end SuffixedLogical
end DosenPetric.Reduced.Gentzen
