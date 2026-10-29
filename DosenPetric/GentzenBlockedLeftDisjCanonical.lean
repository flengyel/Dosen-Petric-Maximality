module

public import DosenPetric.GentzenBlockedLeftDisjTerminalSquares

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedLeftDisj
universe u
variable {P : Type u}

theorem parent_terminal {A B C F H D E : NormalForm P}
    (f : Hom (.conj C (.conj F A)) D) (g : Hom (.conj C (.conj H B)) E) :
    comp (tensor .conj (diag C) (id (.conj (.disj A B) (.conj F H))))
      (comp (assocL .conj C C (.conj (.disj A B) (.conj F H)))
        (DoubleDisjSplice.body (comp (frontChild C F A) f) (comp (frontChild C H B) g))) =
      comp (tensor .conj (id C) (swap .conj (.disj A B) (.conj F H)))
        (comp (parent C F H A B) (tensor .disj f g)) := by
  have hf {V Q W : NormalForm P} (v : Hom (.conj C (.conj V Q)) W) :
      comp (swap .conj (.conj C V) Q) (comp (frontChild C V Q) v) =
        comp (assocL .conj C V Q) v := by
    rw [← Laws.assoc,frontChild_square]
  have ht : tensor .disj (comp (assocL .conj C F A) f) (comp (assocL .conj C H B) g) =
      comp (tensor .disj (assocL .conj C F A) (assocL .conj C H B)) (tensor .disj f g) := by
    rw [Laws.tensor_comp]
  rw [DoubleDisjSplice.body,DisjLogical.disjPair]
  rw [hf,hf,ht]
  have he := congrArg (fun v => comp v
    (comp (ofTerm (Rules.sourceConj (.conj C F) (.conj C H) A B))
      (comp (tensor .disj (assocL .conj C F A) (assocL .conj C H B)) (tensor .disj f g))))
    (parent_input_square C F H (.disj A B))
  simpa only [parent,Laws.assoc] using he

theorem child_terminal {A C F D X R : NormalForm P}
    (h : Hom X (.disj C R)) (f : Hom (.conj C (.conj F A)) D) :
    comp (swap .conj (.conj F X) A) (DoubleDisjSplice.child h (comp (frontChild C F A) f)) =
      comp (terminalCross F X A) (splice h f) := by
  rw [DoubleDisjSplice.child,← Laws.assoc ((sideM P .conj).cross C A F),
    frontChild_head,Splice.context]
  have he := congrArg (fun v => comp v (splice h f)) (child_terminal_input A F X)
  simpa only [Laws.assoc] using he

/-- The terminal disjunction comparison shares the selected formula and the
    original opposite premise across its two children. -/
theorem canonical_equation {A B C F H D E X R : NormalForm P}
    (f : Hom (.conj C (.conj F A)) D) (g : Hom (.conj C (.conj H B)) E)
    (h : Hom X (.disj C R)) :
    splice h (comp (parent C F H A B) (tensor .disj f g)) =
      comp (input F H (.disj A B) X)
        (comp (ofTerm (Rules.sourceConj (.conj F X) (.conj H X) A B))
          (comp (tensor .disj
            (comp (terminalCross F X A) (splice h f))
            (comp (terminalCross H X B) (splice h g))) (BlockedMix.sharedOutput D E R))) := by
  let p := tensor .conj (swap .conj (.conj F H) (.disj A B)) (id X)
  have hr : comp p
      (comp (DoubleDisjSplice.parallelInput (.disj A B) F H X)
        (comp (DisjLogical.disjPair
          (DoubleDisjSplice.child h (comp (frontChild C F A) f))
          (DoubleDisjSplice.child h (comp (frontChild C H B) g)))
          (BlockedMix.sharedOutput D E R))) =
      comp (input F H (.disj A B) X)
        (comp (ofTerm (Rules.sourceConj (.conj F X) (.conj H X) A B))
          (comp (tensor .disj
            (comp (terminalCross F X A) (splice h f))
            (comp (terminalCross H X B) (splice h g))) (BlockedMix.sharedOutput D E R))) := by
    unfold DisjLogical.disjPair
    rw [child_terminal,child_terminal]
    have he := congrArg (fun v => comp v
      (comp (ofTerm (Rules.sourceConj (.conj F X) (.conj H X) A B))
        (comp (tensor .disj
          (comp (terminalCross F X A) (splice h f))
          (comp (terminalCross H X B) (splice h g))) (BlockedMix.sharedOutput D E R))))
      (parallel_input_square F H (.disj A B) X)
    simpa only [p,Laws.assoc] using he
  have he := congrArg (fun v => comp p v)
    (DoubleDisjSplice.equation (comp (frontChild C F A) f) (comp (frontChild C H B) g) h)
  rw [parent_terminal,Splice.context,hr] at he
  have hp : comp p (tensor .conj (swap .conj (.disj A B) (.conj F H)) (id X)) =
      id (.conj (.conj (.conj F H) (.disj A B)) X) := by
    dsimp only [p]
    rw [Laws.tensor_comp,Laws.swap_swap,Laws.id_comp,Laws.tensor_id]
  simpa only [← Laws.assoc,hp,Laws.id_comp] using he

end DosenPetric.Reduced.Gentzen.BlockedLeftDisj
