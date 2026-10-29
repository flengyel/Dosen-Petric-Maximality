module

public import DosenPetric.GentzenBlockedDisjCore
public import DosenPetric.GentzenTerminalFoldPrograms

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedDisj
universe u
variable {P : Type u}

def parallelInput (T F U : List (NormalForm P)) (Q : NormalForm P) :
    StructuralProgram P (T++((F++U)++[Q])) (((T++F)++(T++U))++[Q]) :=
  (ExchangeScript.appendAssoc T (F++U) [Q]).structural.seq
    (((BlockedMix.rightInputRoute T F U).parallel (Route.identity [Q])).program)

/-- The two original child contexts share the fixed input block; the terminal
    logical principal is retained as its own tagged position. -/
theorem parallelInput_square (T F U : List (NormalForm P)) (Q : NormalForm P) :
    comp ((parallelInput T F U Q).arrow .conj)
      (comp (TerminalFold.sourceInput (T++F) (T++U) Q)
        (tensor .conj
          (tensor .conj (ofTerm (append .conj T F).invTerm) (ofTerm (append .conj T U).invTerm))
          (id Q))) =
      comp (ofTerm (append .conj T ((F++U)++[Q])).invTerm)
        (comp (tensor .conj (id (ante T)) (TerminalFold.sourceInput F U Q))
          (comp (assocR .conj (ante T) (.conj (ante F) (ante U)) Q)
            (tensor .conj (BlockedMix.rightSharedInput (ante T) (ante F) (ante U)) (id Q)))) := by
  rw [parallelInput,StructuralProgram.arrow,ExchangeScript.structural_arrow,Route.program_arrow]
  change comp (comp ((ExchangeScript.appendAssoc T (F++U) [Q]).arrow .conj)
    (ofTerm ((BlockedMix.rightInputRoute T F U).parallel (Route.identity [Q])).product)) _ = _
  unfold TerminalFold.sourceInput
  simp only [Laws.assoc]
  rw [← Laws.assoc (ofTerm ((BlockedMix.rightInputRoute T F U).parallel (Route.identity [Q])).product),
    TerminalFold.parallel_out]
  simp only [Laws.assoc,Laws.tensor_comp,Laws.comp_id]
  have hr := BlockedMix.right_input_square T F U
  erw [hr]
  have ht {V W Z : NormalForm P} (a : Hom V W) (b : Hom W Z) :
      tensor .conj (comp a b) (id Q) = comp (tensor .conj a (id Q)) (tensor .conj b (id Q)) := by
    rw [Laws.tensor_comp,Laws.comp_id]
  rw [ht,ht]
  rw [← Laws.assoc ((ExchangeScript.appendAssoc T (F++U) [Q]).arrow .conj),
    ← Laws.assoc (comp ((ExchangeScript.appendAssoc T (F++U) [Q]).arrow .conj)
      (TerminalFold.out (T++(F++U)) Q)),
    Laws.assoc ((ExchangeScript.appendAssoc T (F++U) [Q]).arrow .conj),TerminalFold.out_assoc]
  have hn : comp (assocR .conj (ante T) (ante (F++U)) Q)
      (tensor .conj (tensor .conj (id (ante T)) (ofTerm (append .conj F U).invTerm)) (id Q)) =
      comp (tensor .conj (id (ante T)) (tensor .conj (ofTerm (append .conj F U).invTerm) (id Q)))
        (assocR .conj (ante T) (.conj (ante F) (ante U)) Q) := by
    simpa only [Laws.tensor_id] using
      Laws.assocR_nat .conj (id (ante T)) (ofTerm (append .conj F U).invTerm) (id Q)
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocR .conj (ante T) (ante (F++U)) Q),hn]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id (ante T)) (TerminalFold.out (F++U) Q)),
    Laws.tensor_comp,Laws.id_comp]

end DosenPetric.Reduced.Gentzen.BlockedDisj
