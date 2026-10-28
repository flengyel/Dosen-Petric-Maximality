module

public import DosenPetric.GentzenLogicalHeadRouting

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace G

/-- Route a selected conjunction to a fresh head rule, moving its components below it. -/
theorem conjL_toHead (F U V : List (NormalForm P)) (A B : NormalForm P)
    (h : G P (F ++ A :: B :: U) V) :
    ofTerm ((At.shift F (.here (.conj A B) U)).toHead.left (G.conjL F U V A B h)).denote =
      ofTerm (G.conjL [] (At.shift F (.here (.conj A B) U)).erase V A B
        ((LogicalHeadRouting.components F U A B (.conj A B)).left h)).denote := by
  rw [ExchangeScript.left_denote, denote_conjL, denote_conjL, ExchangeScript.left_denote]
  have hl : ofTerm (Rules.conjLeft F U A B).toTerm = logicalSide .conj F U A B := by
    rw [conjLeft_compare]
    rfl
  have hr : ofTerm (Rules.conjLeft [] (At.shift F (.here (.conj A B) U)).erase A B).toTerm =
      logicalSide .conj [] (At.shift F (.here (.conj A B) U)).erase A B := by
    rw [conjLeft_compare]
    rfl
  rw [hl,hr]
  have hs : comp ((At.shift F (.here (.conj A B) U)).toHead.arrow .conj)
      (logicalSide .conj F U A B) =
      comp (logicalSide .conj [] (At.shift F (.here (.conj A B) U)).erase A B)
        ((LogicalHeadRouting.components F U A B (.conj A B)).arrow .conj) :=
    LogicalHeadRouting.square .conj F U A B
  rw [← Laws.assoc, hs, Laws.assoc]

/-- The independently typed right-hand dual of principal logical head routing. -/
theorem disjR_toHead (Γ Δ Λ : List (NormalForm P)) (A B : NormalForm P)
    (h : G P Γ (Δ ++ A :: B :: Λ)) :
    ofTerm ((At.shift Δ (.here (.disj A B) Λ)).toHead.right (G.disjR Γ Δ Λ A B h)).denote =
      ofTerm (G.disjR Γ [] (At.shift Δ (.here (.disj A B) Λ)).erase A B
        ((LogicalHeadRouting.components Δ Λ A B (.disj A B)).right h)).denote := by
  rw [ExchangeScript.right_denote, denote_disjR, denote_disjR, ExchangeScript.right_denote]
  have hl : ofTerm (Rules.disjRight Δ Λ A B).toTerm = logicalSide .disj Δ Λ A B := by
    rw [disjRight_compare]
    rfl
  have hr : ofTerm (Rules.disjRight [] (At.shift Δ (.here (.disj A B) Λ)).erase A B).toTerm =
      logicalSide .disj [] (At.shift Δ (.here (.disj A B) Λ)).erase A B := by
    rw [disjRight_compare]
    rfl
  rw [hl,hr]
  have hs : comp (logicalSide .disj Δ Λ A B) ((At.shift Δ (.here (.disj A B) Λ)).toHead.arrow .disj) =
      comp ((LogicalHeadRouting.components Δ Λ A B (.disj A B)).arrow .disj)
        (logicalSide .disj [] (At.shift Δ (.here (.disj A B) Λ)).erase A B) :=
    LogicalHeadRouting.square .disj Δ Λ A B
  rw [Laws.assoc, hs, ← Laws.assoc]

end G
end DosenPetric.Reduced.Gentzen
