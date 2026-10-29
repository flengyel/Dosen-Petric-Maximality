module

public import DosenPetric.GentzenBlockedRightConjOutput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedRightConj
universe u
variable {P : Type u}

theorem parallel_denote {Γ Θ D E Y T J : List (NormalForm P)} {A B C : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (f : G P Γ (A::C::D)) (g : G P Θ (B::C::E)) (h : G P (C::T) J) :
    ofTerm (parallel p q (G.cut ((HeadRouting.front [A] D C).right f) h)
      (G.cut ((HeadRouting.front [B] E C).right g) h)).denote =
      comp (ofTerm (append .conj T (Γ++Θ)).invTerm)
        (comp (tensor .conj (id (ante T)) (ofTerm (append .conj Γ Θ).invTerm))
          (comp (BlockedMix.rightSharedInput (ante T) (ante Γ) (ante Θ))
            (comp (tensor .conj
              (DoubleConjSplice.child (ofTerm f.denote) (ofTerm h.denote))
              (DoubleConjSplice.child (ofTerm g.denote) (ofTerm h.denote)))
              (comp (ofTerm (Term.mixedDisj A (.disj (succ J) (succ D)) B (.disj (succ J) (succ E))))
                (comp (sharedOutput (succ J) (.conj A B) (p.sideArrow .disj) (q.sideArrow .disj))
                  (ofTerm (append .disj J (.conj A B::Y)).toTerm)))))) := by
  rw [parallel,ExchangeScript.right_denote,StructuralProgram.left_denote,
    StructuralProgram.right_denote,Route.program_arrow,Route.program_arrow,G.denote_conjR]
  simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id]
  rw [child_denote,child_denote]
  have ht : tensor .conj
      (comp (ofTerm (append .conj T Γ).invTerm)
        (comp (DoubleConjSplice.child (ofTerm f.denote) (ofTerm h.denote))
          (tensor .disj (id A) (ofTerm (append .disj J D).toTerm))))
      (comp (ofTerm (append .conj T Θ).invTerm)
        (comp (DoubleConjSplice.child (ofTerm g.denote) (ofTerm h.denote))
          (tensor .disj (id B) (ofTerm (append .disj J E).toTerm)))) =
      comp (tensor .conj (ofTerm (append .conj T Γ).invTerm) (ofTerm (append .conj T Θ).invTerm))
        (comp (tensor .conj
          (DoubleConjSplice.child (ofTerm f.denote) (ofTerm h.denote))
          (DoubleConjSplice.child (ofTerm g.denote) (ofTerm h.denote)))
          (tensor .conj (tensor .disj (id A) (ofTerm (append .disj J D).toTerm))
            (tensor .disj (id B) (ofTerm (append .disj J E).toTerm)))) := by
    simp only [Laws.tensor_comp]
  have hm := mixedDisj_nat (id A) (ofTerm (append .disj J D).toTerm)
    (id B) (ofTerm (append .disj J E).toTerm)
  rw [Laws.tensor_id] at hm
  rw [ht]
  simp only [Laws.assoc]
  erw [← Laws.assoc (tensor .conj (tensor .disj (id A) (ofTerm (append .disj J D).toTerm))
    (tensor .disj (id B) (ofTerm (append .disj J E).toTerm))),← hm]
  simp only [Laws.assoc]
  erw [output_square]
  erw [← Laws.assoc ((BlockedMix.rightInputRoute T Γ Θ).sideArrow .conj),
    ← Laws.assoc (comp ((BlockedMix.rightInputRoute T Γ Θ).sideArrow .conj)
      (ofTerm (append .conj (T++Γ) (T++Θ)).invTerm)),
    Laws.assoc ((BlockedMix.rightInputRoute T Γ Θ).sideArrow .conj),BlockedMix.right_input_square]
  simp only [Laws.assoc]

theorem headParent_equation {Γ Θ D E Y T J : List (NormalForm P)} {A B C : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (f : G P Γ (A::C::D)) (g : G P Θ (B::C::E)) (h : G P (C::T) J) :
    ofTerm (G.cut (headParent p q f g) h).denote =
      ofTerm (parallel p q (G.cut ((HeadRouting.front [A] D C).right f) h)
        (G.cut ((HeadRouting.front [B] E C).right g) h)).denote := by
  rw [cut_splice,headParent_denote,Splice.input,shared_equation,parallel_denote]
  simp only [Laws.assoc]

theorem parallel_congr {Γ Θ D E Y T J : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (k k' : G P (T++Γ) (J++(A::D))) (l l' : G P (T++Θ) (J++(B::E)))
    (hk : ofTerm k.denote = ofTerm k'.denote) (hl : ofTerm l.denote = ofTerm l'.denote) :
    ofTerm (parallel p q k l).denote = ofTerm (parallel p q k' l').denote := by
  unfold parallel
  simp only [ExchangeScript.right_denote,StructuralProgram.left_denote,
    StructuralProgram.right_denote,G.denote_conjR,Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id,hk,hl]

end DosenPetric.Reduced.Gentzen.BlockedRightConj
