module

public import DosenPetric.GentzenCutResidueTransport

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace CutCommutation

/-- A native conjunction-left comparison commutes with a selected cut through its
    deletion square. The two residual contexts are specified by actual lists. -/
theorem same_conjL_head {Γ Δ F U R V Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (C :: Δ)) (g : G P (F ++ A :: B :: U) Λ)
    (p : ExchangeScript P (C :: (R ++ .conj A B :: V)) (F ++ .conj A B :: U))
    (q : ExchangeScript P (C :: (R ++ A :: B :: V)) (F ++ A :: B :: U))
    (hs : comp (p.arrow .conj) (logicalSide .conj F U A B) =
      comp (tensor .conj (id C) (logicalSide .conj R V A B)) (q.arrow .conj)) :
    ofTerm (G.cut f (p.left (G.conjL F U Λ A B g))).denote =
      ofTerm (SuffixedLogical.conjL R V Γ (Λ ++ Δ) A B (G.cut f (q.left g))).denote := by
  rw [cut_splice,ExchangeScript.left_denote,G.denote_conjL,conjLeft_compare,
    SuffixedLogical.conjL_denote,cut_splice,ExchangeScript.left_denote]
  change comp _ (comp (splice (ofTerm f.denote)
    (comp (p.arrow .conj) (comp (logicalSide .conj F U A B) (ofTerm g.denote)))) _) = _
  rw [← Laws.assoc (p.arrow .conj),hs,Laws.assoc,Splice.context]
  have hi : comp (suffixLogicalSide .conj R V Γ A B)
      (ofTerm (append .conj (R ++ A :: B :: V) Γ).invTerm) =
      comp (ofTerm (append .conj (R ++ .conj A B :: V) Γ).invTerm)
        (tensor .conj (logicalSide .conj R V A B) (id (ante Γ))) :=
    suffixLogicalSide_split .conj R V Γ A B
  simp only [Laws.assoc]
  rw [← Laws.assoc (suffixLogicalSide .conj R V Γ A B),hi,Laws.assoc]

/-- The independently typed disjunction-right equation uses the opposite-side
    deletion square and preserves the exact residual output order. -/
theorem same_disjR_head {Γ F U R V Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (F ++ A :: B :: U)) (g : G P (C :: Θ) Λ)
    (p : ExchangeScript P (C :: (R ++ .disj A B :: V)) (F ++ .disj A B :: U))
    (q : ExchangeScript P (C :: (R ++ A :: B :: V)) (F ++ A :: B :: U))
    (hs : comp (logicalSide .disj F U A B) (p.arrow .disj) =
      comp (q.arrow .disj) (tensor .disj (id C) (logicalSide .disj R V A B))) :
    ofTerm (G.cut (p.right (G.disjR Γ F U A B f)) g).denote =
      ofTerm (PrefixedLogical.disjR (Θ ++ Γ) Λ R V A B (G.cut (q.right f) g)).denote := by
  rw [cut_splice,ExchangeScript.right_denote,G.denote_disjR,disjRight_compare,
    PrefixedLogical.disjR_denote,cut_splice,ExchangeScript.right_denote]
  change comp _ (comp (splice
    (comp (comp (ofTerm f.denote) (logicalSide .disj F U A B)) (p.arrow .disj))
    (ofTerm g.denote)) _) = _
  rw [Laws.assoc (ofTerm f.denote),hs,← Laws.assoc (ofTerm f.denote),Splice.residual]
  have ho : comp (ofTerm (append .disj Λ (R ++ A :: B :: V)).toTerm)
      (prefixSide .disj Λ (logicalSide .disj R V A B)) =
      comp (tensor .disj (id (succ Λ)) (logicalSide .disj R V A B))
        (ofTerm (append .disj Λ (R ++ .disj A B :: V)).toTerm) :=
    prefixSide_split .disj Λ _
  simp only [Laws.assoc]
  rw [ho]

end CutCommutation
end DosenPetric.Reduced.Gentzen
