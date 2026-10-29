module

public import DosenPetric.GentzenBlockedLeftDisjCutCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedLeftDisj
universe u
variable {P : Type u}

theorem parallel_denote {Y F H D E I R : List (NormalForm P)} {A B C : NormalForm P}
    (p : Route Y F) (q : Route Y H) (h : G P I (C::R))
    (f : G P (C::(F++[A])) D) (g : G P (C::(H++[B])) E) :
    ofTerm (parallel p q (G.cut h f) (G.cut h g)).denote =
      comp (ofTerm (append .conj (Y++[.disj A B]) I).invTerm)
        (comp (tensor .conj (TerminalFold.out Y (.disj A B)) (id (ante I)))
          (comp (sharedInput (p.sideArrow .conj) (q.sideArrow .conj) (.disj A B))
            (comp (ofTerm (Rules.sourceConj (.conj (ante F) (ante I)) (.conj (ante H) (ante I)) A B))
              (comp (tensor .disj
                (comp (terminalCross (ante F) (ante I) A) (splice (ofTerm h.denote) (childArrow f)))
                (comp (terminalCross (ante H) (ante I) B) (splice (ofTerm h.denote) (childArrow g))))
                (comp (BlockedMix.sharedOutput (succ D) (succ E) (succ R))
                  (comp (tensor .disj (ofTerm (append .disj D E).toTerm) (id (succ R)))
                    (ofTerm (append .disj (D++E) R).toTerm))))))) := by
  rw [parallel,ExchangeScript.left_denote,StructuralProgram.left_denote,
    StructuralProgram.right_denote,TerminalFold.disjLLast_denote,Route.program_arrow,Route.program_arrow]
  simp only [Laws.assoc]
  rw [← Laws.assoc (ofTerm (Rules.sourceConj (ante (F++I)) (ante (H++I)) A B)),
    sourceConj_split,child_cut_denote,child_cut_denote]
  have ht : tensor .disj
      (comp (terminalCross (ante F) (ante I) A)
        (comp (splice (ofTerm h.denote) (childArrow f)) (ofTerm (append .disj D R).toTerm)))
      (comp (terminalCross (ante H) (ante I) B)
        (comp (splice (ofTerm h.denote) (childArrow g)) (ofTerm (append .disj E R).toTerm))) =
      comp (tensor .disj
        (comp (terminalCross (ante F) (ante I) A) (splice (ofTerm h.denote) (childArrow f)))
        (comp (terminalCross (ante H) (ante I) B) (splice (ofTerm h.denote) (childArrow g))))
        (tensor .disj (ofTerm (append .disj D R).toTerm) (ofTerm (append .disj E R).toTerm)) := by
    simp only [Laws.tensor_comp,Laws.assoc]
  simp only [Laws.assoc]
  rw [ht]
  simp only [Laws.assoc]
  erw [BlockedMix.output_square E D R]
  erw [← Laws.assoc ((terminalExchange Y (.disj A B) I).arrow .conj),
    ← Laws.assoc (comp ((terminalExchange Y (.disj A B) I).arrow .conj)
      (ofTerm ((BlockedMix.inputRoute q p I).parallel (Route.identity [.disj A B])).product)),
    ← Laws.assoc (comp (comp ((terminalExchange Y (.disj A B) I).arrow .conj)
      (ofTerm ((BlockedMix.inputRoute q p I).parallel (Route.identity [.disj A B])).product))
      (TerminalFold.sourceInput (F++I) (H++I) (.disj A B)))]
  have he := parallelInput_square p q (.disj A B) I
  simp only [← Laws.assoc] at he
  erw [he]
  simp only [Laws.assoc]

/-- The actual head-selected Gentzen parent has the exact two-cut reconstruction. -/
theorem headParent_equation {Y F H D E I R : List (NormalForm P)} {A B C : NormalForm P}
    (p : Route Y F) (q : Route Y H) (h : G P I (C::R))
    (f : G P (C::(F++[A])) D) (g : G P (C::(H++[B])) E) :
    ofTerm (G.cut h (headParent p q f g)).denote =
      ofTerm (parallel p q (G.cut h f) (G.cut h g)).denote := by
  rw [cut_splice,headParent_denote,Splice.context,Splice.output,shared_equation,parallel_denote]
  simp only [Laws.assoc]

theorem parallel_congr {Y F H D E I R : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y F) (q : Route Y H)
    (k k' : G P ((F++[A])++I) (D++R)) (l l' : G P ((H++[B])++I) (E++R))
    (hk : ofTerm k.denote = ofTerm k'.denote) (hl : ofTerm l.denote = ofTerm l'.denote) :
    ofTerm (parallel p q k l).denote = ofTerm (parallel p q k' l').denote := by
  unfold parallel
  simp only [ExchangeScript.left_denote,StructuralProgram.left_denote,StructuralProgram.right_denote,
    TerminalFold.disjLLast_denote,hk,hl]

end DosenPetric.Reduced.Gentzen.BlockedLeftDisj
