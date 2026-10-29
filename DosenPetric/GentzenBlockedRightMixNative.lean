module

public import DosenPetric.GentzenBlockedRightMixCoordinates
public import DosenPetric.GentzenHeadRoutes

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedMix
universe u
variable {P : Type u}

def rightHeadParent {Y F H Γ Θ : List (NormalForm P)} {C : NormalForm P}
    (p : Route Y F) (q : Route Y H) (f : G P Γ (C::F)) (g : G P Θ (C::H)) :
    G P (Θ++Γ) (C::Y) :=
  ((q.head C).append (p.head C)).program.right (G.mix f g)

theorem rightHeadParent_denote {Y F H Γ Θ : List (NormalForm P)} {C : NormalForm P}
    (p : Route Y F) (q : Route Y H) (f : G P Γ (C::F)) (g : G P Θ (C::H)) :
    ofTerm (rightHeadParent p q f g).denote =
      comp (ofTerm (append .conj Θ Γ).invTerm)
        (rightSharedParent (p.sideArrow .disj) (q.sideArrow .disj)
          (ofTerm f.denote) (ofTerm g.denote)) := by
  rw [rightHeadParent,StructuralProgram.right_denote,Route.program_arrow]
  change comp (ofTerm (Rules.mix f.denote g.denote)) _ = _
  simp only [Rules.mix,ofTerm_comp,ofTerm_tensor,mix_term,Laws.assoc]
  have he := Route.append_split .disj (q.head C) (p.head C)
  rw [Route.head_side,Route.head_side] at he
  dsimp only [side,sideD,sideM,disjMonoidal,opposite,category,split,disjDiagonal,DiagonalData.pair] at he
  erw [he]
  rfl

theorem right_output_square_disj {Y F H : List (NormalForm P)}
    (p : Route Y F) (q : Route Y H) (J : List (NormalForm P)) :
    comp (tensor .disj (ofTerm (append .disj J H).toTerm) (ofTerm (append .disj J F).toTerm))
      (comp (ofTerm (append .disj (J++H) (J++F)).toTerm)
        ((rightOutputRoute p q J).sideArrow .disj)) =
      comp (rightSharedOutput (p.sideArrow .disj) (q.sideArrow .disj))
        (ofTerm (append .disj J Y).toTerm) := by
  have he := right_output_square .disj p q J
  dsimp only [side,sideD,sideM,disjMonoidal,opposite,category,split,disjDiagonal,DiagonalData.pair] at he
  simpa only [rightSharedOutput,copair,Laws.assoc] using he

theorem rightParallel_denote {Y F H Γ Θ I J : List (NormalForm P)} {C : NormalForm P}
    (p : Route Y F) (q : Route Y H) (f : G P Γ (C::F)) (g : G P Θ (C::H))
    (h : G P (C::I) J) :
    ofTerm (rightParallel p q (G.cut f h) (G.cut g h)).denote =
      comp (ofTerm (append .conj I (Θ++Γ)).invTerm)
        (comp (tensor .conj (id (ante I)) (ofTerm (append .conj Θ Γ).invTerm))
          (comp (rightSharedInput (ante I) (ante Θ) (ante Γ))
            (comp (tensor .conj (splice (ofTerm g.denote) (ofTerm h.denote))
              (splice (ofTerm f.denote) (ofTerm h.denote)))
              (comp (mix (.disj (succ J) (succ H)) (.disj (succ J) (succ F)))
                (comp (rightSharedOutput (p.sideArrow .disj) (q.sideArrow .disj))
                  (ofTerm (append .disj J Y).toTerm)))))) := by
  rw [rightParallel,StructuralProgram.left_denote,StructuralProgram.right_denote]
  change comp _ (comp (ofTerm (Rules.mix (G.cut f h).denote (G.cut g h).denote)) _) = _
  simp only [Rules.mix,ofTerm_comp,ofTerm_tensor,mix_term]
  rw [cut_splice,cut_splice,Route.program_arrow,Route.program_arrow]
  have ht : tensor .conj
      (comp (ofTerm (append .conj I Θ).invTerm)
        (comp (splice (ofTerm g.denote) (ofTerm h.denote)) (ofTerm (append .disj J H).toTerm)))
      (comp (ofTerm (append .conj I Γ).invTerm)
        (comp (splice (ofTerm f.denote) (ofTerm h.denote)) (ofTerm (append .disj J F).toTerm))) =
      comp (tensor .conj (ofTerm (append .conj I Θ).invTerm) (ofTerm (append .conj I Γ).invTerm))
        (comp (tensor .conj (splice (ofTerm g.denote) (ofTerm h.denote))
          (splice (ofTerm f.denote) (ofTerm h.denote)))
          (tensor .conj (ofTerm (append .disj J H).toTerm) (ofTerm (append .disj J F).toTerm))) := by
    simp only [Laws.tensor_comp]
  rw [ht]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (ofTerm (append .disj J H).toTerm)
    (ofTerm (append .disj J F).toTerm)),← Laws.mix_nat]
  simp only [Laws.assoc]
  rw [right_output_square_disj]
  rw [← Laws.assoc ((rightInputRoute I Θ Γ).sideArrow .conj),
    ← Laws.assoc (comp ((rightInputRoute I Θ Γ).sideArrow .conj)
      (ofTerm (append .conj (I++Θ) (I++Γ)).invTerm)),
    Laws.assoc ((rightInputRoute I Θ Γ).sideArrow .conj),right_input_square]
  simp only [Laws.assoc]

theorem rightHeadParent_equation {Y F H Γ Θ I J : List (NormalForm P)} {C : NormalForm P}
    (p : Route Y F) (q : Route Y H) (f : G P Γ (C::F)) (g : G P Θ (C::H))
    (h : G P (C::I) J) :
    ofTerm (G.cut (rightHeadParent p q f g) h).denote =
      ofTerm (rightParallel p q (G.cut f h) (G.cut g h)).denote := by
  rw [cut_splice,rightHeadParent_denote,Splice.input,right_shared_splice,rightParallel_denote]
  simp only [Laws.assoc]

end DosenPetric.Reduced.Gentzen.BlockedMix
