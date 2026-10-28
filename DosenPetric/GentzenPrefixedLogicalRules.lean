module

public import DosenPetric.GentzenPrefixLogical

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PrefixedLogical

/-- Apply the actual conjunction-left rule inside a prefixed context. -/
def conjL (K F U Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P (K ++ (F ++ A :: B :: U)) Δ) : G P (K ++ (F ++ .conj A B :: U)) Δ :=
  (ExchangeScript.appendAssoc K F (.conj A B :: U)).left
    (G.conjL (K ++ F) U Δ A B ((ExchangeScript.appendAssoc K F (A :: B :: U)).inverse.left f))

theorem conjL_denote (K F U Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P (K ++ (F ++ A :: B :: U)) Δ) :
    ofTerm (conjL K F U Δ A B f).denote =
      comp (prefixSide .conj K (logicalSide .conj F U A B)) (ofTerm f.denote) := by
  unfold conjL
  rw [ExchangeScript.left_denote,G.denote_conjL,ExchangeScript.left_denote,conjLeft_compare]
  change comp _ (comp (logicalSide .conj (K ++ F) U A B) (comp _ (ofTerm f.denote))) = _
  have he := congrArg (fun k => comp k (ofTerm f.denote)) (prefixSide_logical .conj K F U A B)
  dsimp only [side,category] at he
  simpa only [Laws.assoc] using he

theorem conjL_count (K F U Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P (K ++ (F ++ A :: B :: U)) Δ) :
    (conjL K F U Δ A B f).cutCount = f.cutCount := by
  simp only [conjL,ExchangeScript.left_count,G.cutCount]

theorem conjL_atomized (K F U Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P (K ++ (F ++ A :: B :: U)) Δ) :
    (conjL K F U Δ A B f).Atomized ↔ f.Atomized := by
  simp only [conjL,ExchangeScript.left_atomized,G.Atomized]

/-- Apply the actual disjunction-right rule inside a prefixed context. -/
def disjR (Γ K F U : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ (K ++ (F ++ A :: B :: U))) : G P Γ (K ++ (F ++ .disj A B :: U)) :=
  (ExchangeScript.appendAssoc K F (.disj A B :: U)).right
    (G.disjR Γ (K ++ F) U A B ((ExchangeScript.appendAssoc K F (A :: B :: U)).inverse.right f))

theorem disjR_denote (Γ K F U : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ (K ++ (F ++ A :: B :: U))) :
    ofTerm (disjR Γ K F U A B f).denote =
      comp (ofTerm f.denote) (prefixSide .disj K (logicalSide .disj F U A B)) := by
  unfold disjR
  rw [ExchangeScript.right_denote,G.denote_disjR,ExchangeScript.right_denote,disjRight_compare]
  change comp (comp (comp (ofTerm f.denote) _) (logicalSide .disj (K ++ F) U A B)) _ = _
  have he := congrArg (fun k => comp (ofTerm f.denote) k) (prefixSide_logical .disj K F U A B)
  dsimp only [side,category,opposite] at he
  simpa only [Laws.assoc] using he

theorem disjR_count (Γ K F U : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ (K ++ (F ++ A :: B :: U))) :
    (disjR Γ K F U A B f).cutCount = f.cutCount := by
  simp only [disjR,ExchangeScript.right_count,G.cutCount]

theorem disjR_atomized (Γ K F U : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ (K ++ (F ++ A :: B :: U))) :
    (disjR Γ K F U A B f).Atomized ↔ f.Atomized := by
  simp only [disjR,ExchangeScript.right_atomized,G.Atomized]

end PrefixedLogical
end DosenPetric.Reduced.Gentzen
