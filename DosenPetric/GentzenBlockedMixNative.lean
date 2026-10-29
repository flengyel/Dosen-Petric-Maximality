module

public import DosenPetric.GentzenBlockedMixCoordinates
public import DosenPetric.GentzenHeadRoutes

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedMix
universe u
variable {P : Type u}

/-- Place both selected child inputs at the same fresh head before mixing. -/
def headParent {Y F H D E : List (NormalForm P)} {C : NormalForm P}
    (p : Route Y F) (q : Route Y H) (f : G P (C::F) D) (g : G P (C::H) E) :
    G P (C::Y) (E++D) :=
  ((q.head C).append (p.head C)).program.left (G.mix f g)

theorem headParent_denote {Y F H D E : List (NormalForm P)} {C : NormalForm P}
    (p : Route Y F) (q : Route Y H) (f : G P (C::F) D) (g : G P (C::H) E) :
    ofTerm (headParent p q f g).denote =
      comp (sharedParent (p.sideArrow .conj) (q.sideArrow .conj)
        (ofTerm f.denote) (ofTerm g.denote)) (ofTerm (append .disj E D).toTerm) := by
  rw [headParent,StructuralProgram.left_denote,Route.program_arrow]
  change comp _ (ofTerm (Rules.mix f.denote g.denote)) = _
  simp only [Rules.mix,ofTerm_comp,ofTerm_tensor,mix_term]
  rw [← Laws.assoc]
  have he := Route.append_split .conj (q.head C) (p.head C)
  dsimp only [side,sideD,sideM,category,split,conjDiagonal,DiagonalData.pair] at he
  rw [he,Route.head_side,Route.head_side]
  dsimp only [sharedParent,pair,side,sideM,conjMonoidal,category]
  simp only [Laws.assoc]

/-- The native parallel reconstruction in contextual splice coordinates. -/
theorem parallel_denote {Y F H D E I R : List (NormalForm P)} {C : NormalForm P}
    (p : Route Y F) (q : Route Y H) (f : G P (C::F) D) (g : G P (C::H) E)
    (h : G P I (C::R)) :
    ofTerm (parallel p q (G.cut h f) (G.cut h g)).denote =
      comp (ofTerm (append .conj Y I).invTerm)
        (comp (sharedInput (p.sideArrow .conj) (q.sideArrow .conj))
          (comp (tensor .conj (splice (ofTerm h.denote) (ofTerm g.denote))
            (splice (ofTerm h.denote) (ofTerm f.denote)))
            (comp (mix (.disj (succ E) (succ R)) (.disj (succ D) (succ R)))
              (comp (sharedOutput (succ E) (succ D) (succ R))
                (comp (tensor .disj (ofTerm (append .disj E D).toTerm) (id (succ R)))
                  (ofTerm (append .disj (E++D) R).toTerm)))))) := by
  rw [parallel,StructuralProgram.left_denote,StructuralProgram.right_denote]
  change comp _ (comp (ofTerm (Rules.mix (G.cut h f).denote (G.cut h g).denote)) _) = _
  simp only [Rules.mix,ofTerm_comp,ofTerm_tensor,mix_term]
  rw [cut_splice,cut_splice]
  rw [Route.program_arrow,Route.program_arrow]
  have ht : tensor .conj
      (comp (ofTerm (append .conj H I).invTerm)
        (comp (splice (ofTerm h.denote) (ofTerm g.denote)) (ofTerm (append .disj E R).toTerm)))
      (comp (ofTerm (append .conj F I).invTerm)
        (comp (splice (ofTerm h.denote) (ofTerm f.denote)) (ofTerm (append .disj D R).toTerm))) =
      comp (tensor .conj (ofTerm (append .conj H I).invTerm) (ofTerm (append .conj F I).invTerm))
        (comp (tensor .conj (splice (ofTerm h.denote) (ofTerm g.denote))
          (splice (ofTerm h.denote) (ofTerm f.denote)))
          (tensor .conj (ofTerm (append .disj E R).toTerm) (ofTerm (append .disj D R).toTerm))) := by
    simp only [Laws.tensor_comp]
  rw [ht]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (ofTerm (append .disj E R).toTerm)
    (ofTerm (append .disj D R).toTerm)),← Laws.mix_nat]
  simp only [Laws.assoc]
  rw [output_square]
  rw [← Laws.assoc ((inputRoute p q I).sideArrow .conj),
    ← Laws.assoc (comp ((inputRoute p q I).sideArrow .conj)
      (ofTerm (append .conj (H++I) (F++I)).invTerm)),
    Laws.assoc ((inputRoute p q I).sideArrow .conj),input_square_conj]
  simp only [Laws.assoc]

/-- Exact native equation, before arbitrary selected-tag adapters. -/
theorem headParent_equation {Y F H D E I R : List (NormalForm P)} {C : NormalForm P}
    (p : Route Y F) (q : Route Y H) (f : G P (C::F) D) (g : G P (C::H) E)
    (h : G P I (C::R)) :
    ofTerm (G.cut h (headParent p q f g)).denote =
      ofTerm (parallel p q (G.cut h f) (G.cut h g)).denote := by
  rw [cut_splice,headParent_denote,Splice.output,shared_splice,parallel_denote]
  simp only [Laws.assoc]

end DosenPetric.Reduced.Gentzen.BlockedMix
