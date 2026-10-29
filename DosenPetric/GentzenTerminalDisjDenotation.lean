module

public import DosenPetric.GentzenTerminalFoldCoordinates
public import DosenPetric.GentzenTerminalLogicalNaturality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.TerminalFold
universe u
variable {P : Type u}

def sourceInput (F U : List (NormalForm P)) (Q : NormalForm P) :
    Hom (ante ((F++U)++[Q])) (.conj (.conj (ante F) (ante U)) Q) :=
  comp (out (F++U) Q) (tensor .conj (ofTerm (append .conj F U).invTerm) (id Q))

theorem sourceInput_eq (F U : List (NormalForm P)) (Q : NormalForm P) :
    comp (ofTerm (Route.toTail (F++U) Q).product)
      (comp (tensor .conj (id Q) (ofTerm (append .conj F U).invTerm))
        (swap .conj Q (.conj (ante F) (ante U)))) = sourceInput F U Q := by
  rw [toTail_eq]
  simp only [Laws.assoc]
  rw [← Laws.assoc (swap .conj (ante (F++U)) Q),Laws.swap_nat]
  simp only [Laws.assoc]
  rw [Laws.swap_swap,Laws.comp_id]
  rfl

/-- Denotation of the actual three-exchange source macro in terminal coordinates. -/
theorem disjLLast_denote {F U Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ) :
    ofTerm (BlockedSource.disjLLast f g).denote =
      comp (sourceInput F U (.disj A B))
        (comp (ofTerm (Rules.sourceConj (ante F) (ante U) A B))
          (comp (tensor .disj
            (comp (into F A) (ofTerm f.denote))
            (comp (into U B) (ofTerm g.denote)))
            (ofTerm (append .disj Δ Λ).toTerm))) := by
  rw [Rules.terminalDisjLeft_denote]
  simp only [Rules.terminalDisjLeft,Rules.disjLeft,ofTerm_comp,ofTerm_tensor,ofTerm_id,term_swap]
  have hf : comp (swap .conj (ante F) A)
      (comp (ofTerm (Route.toHead F A).product) (ofTerm f.denote)) =
      comp (into F A) (ofTerm f.denote) := by
    rw [toHead_eq,← Laws.assoc,← Laws.assoc,Laws.swap_swap,Laws.id_comp]
  have hg : comp (swap .conj (ante U) B)
      (comp (ofTerm (Route.toHead U B).product) (ofTerm g.denote)) =
      comp (into U B) (ofTerm g.denote) := by
    rw [toHead_eq,← Laws.assoc,← Laws.assoc,Laws.swap_swap,Laws.id_comp]
  rw [← Laws.assoc (tensor .disj (swap .conj (ante F) A) (swap .conj (ante U) B)),
    Laws.tensor_comp,hf,hg]
  rw [← Laws.assoc (ofTerm (Route.toTail (F++U) (.disj A B)).product),
    ← Laws.assoc (comp (ofTerm (Route.toTail (F++U) (.disj A B)).product)
      (tensor .conj (id (.disj A B)) (ofTerm (append .conj F U).invTerm))),
    Laws.assoc (ofTerm (Route.toTail (F++U) (.disj A B)).product),sourceInput_eq]

end DosenPetric.Reduced.Gentzen.TerminalFold
