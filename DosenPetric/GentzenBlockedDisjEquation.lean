module

public import DosenPetric.GentzenBlockedDisjNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedDisj
universe u
variable {P : Type u}

/-- Both child cuts use the same original right premise. The input and output
    contractions remain explicit in the reconstruction. -/
theorem parallel_denote {F U D E Y T J : List (NormalForm P)} {A B C : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (f : G P (F++[A]) (C::D)) (g : G P (U++[B]) (C::E)) (h : G P (C::T) J) :
    ofTerm (parallel p q (G.cut f h) (G.cut g h)).denote =
      comp (ofTerm (append .conj T ((F++U)++[.disj A B])).invTerm)
        (comp (tensor .conj (id (ante T)) (TerminalFold.sourceInput F U (.disj A B)))
          (comp (assocR .conj (ante T) (.conj (ante F) (ante U)) (.disj A B))
            (comp (tensor .conj (BlockedMix.rightSharedInput (ante T) (ante F) (ante U))
                (id (.disj A B)))
              (comp (ofTerm (Rules.sourceConj (.conj (ante T) (ante F))
                  (.conj (ante T) (ante U)) A B))
                (comp (tensor .disj
                    (comp (assocL .conj (ante T) (ante F) A)
                      (splice (comp (TerminalFold.into F A) (ofTerm f.denote)) (ofTerm h.denote)))
                    (comp (assocL .conj (ante T) (ante U) B)
                      (splice (comp (TerminalFold.into U B) (ofTerm g.denote)) (ofTerm h.denote))))
                  (comp (BlockedMix.rightSharedOutput (q.sideArrow .disj) (p.sideArrow .disj))
                    (ofTerm (append .disj J Y).toTerm))))))) := by
  rw [parallel,StructuralProgram.left_denote,StructuralProgram.right_denote,
    TerminalFold.disjLLast_denote,Route.program_arrow]
  simp only [Laws.assoc]
  rw [← Laws.assoc (ofTerm (Rules.sourceConj (ante (T++F)) (ante (T++U)) A B)),
    sourceConj_split,child_cut_denote,child_cut_denote]
  have ht : tensor .disj
      (comp (assocL .conj (ante T) (ante F) A)
        (comp (splice (comp (TerminalFold.into F A) (ofTerm f.denote)) (ofTerm h.denote))
          (ofTerm (append .disj J D).toTerm)))
      (comp (assocL .conj (ante T) (ante U) B)
        (comp (splice (comp (TerminalFold.into U B) (ofTerm g.denote)) (ofTerm h.denote))
          (ofTerm (append .disj J E).toTerm))) =
      comp (tensor .disj
        (comp (assocL .conj (ante T) (ante F) A)
          (splice (comp (TerminalFold.into F A) (ofTerm f.denote)) (ofTerm h.denote)))
        (comp (assocL .conj (ante T) (ante U) B)
          (splice (comp (TerminalFold.into U B) (ofTerm g.denote)) (ofTerm h.denote))))
        (tensor .disj (ofTerm (append .disj J D).toTerm) (ofTerm (append .disj J E).toTerm)) := by
    simp only [Laws.tensor_comp,Laws.assoc]
  simp only [Laws.assoc]
  rw [ht]
  simp only [Laws.assoc]
  erw [BlockedMix.right_output_square_disj q p J]
  rw [← Laws.assoc ((parallelInput T F U (.disj A B)).arrow .conj),
    ← Laws.assoc (comp ((parallelInput T F U (.disj A B)).arrow .conj)
      (TerminalFold.sourceInput (T++F) (T++U) (.disj A B))),
    Laws.assoc ((parallelInput T F U (.disj A B)).arrow .conj),parallelInput_square]
  simp only [Laws.assoc]

/-- The native terminal-disjunction parent equals the two-cut reconstruction. -/
theorem headParent_equation {F U D E Y T J : List (NormalForm P)} {A B C : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (f : G P (F++[A]) (C::D)) (g : G P (U++[B]) (C::E)) (h : G P (C::T) J) :
    ofTerm (G.cut (headParent p q f g) h).denote =
      ofTerm (parallel p q (G.cut f h) (G.cut g h)).denote := by
  rw [cut_splice,headParent_denote,Splice.input,parallel_denote]
  have he := head_right_shared_splice (p.sideArrow .disj) (q.sideArrow .disj)
    (comp (TerminalFold.into F A) (ofTerm f.denote))
    (comp (TerminalFold.into U B) (ofTerm g.denote)) (ofTerm h.denote)
  have he' := congrArg (fun v =>
    comp (ofTerm (append .conj T ((F++U)++[.disj A B])).invTerm)
      (comp (tensor .conj (id (ante T)) (TerminalFold.sourceInput F U (.disj A B)))
        (comp (assocR .conj (ante T) (.conj (ante F) (ante U)) (.disj A B))
          (comp v (ofTerm (append .disj J Y).toTerm))))) he
  simp only [Laws.assoc] at he'
  rw [← Laws.assoc (assocR .conj (ante T) (.conj (ante F) (ante U)) (.disj A B)),
    Laws.assocR_L,Laws.id_comp] at he'
  simpa only [Laws.assoc] using he'

end DosenPetric.Reduced.Gentzen.BlockedDisj
