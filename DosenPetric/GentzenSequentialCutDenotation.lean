module

public import DosenPetric.GentzenSequentialContractionHead

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialRepair
universe u
variable {P : Type u}

theorem tail_decoded (o : Op) (F I : List (NormalForm P)) :
    (side P o).comp ((tailRoute F I).sideArrow o)
      ((side P o).comp (split o (F++I) I)
        ((sideM P o).tensor (split o F I) ((side P o).id (fold o I)))) =
      (side P o).comp (split o F I)
        ((side P o).comp ((sideM P o).tensor ((side P o).id (fold o F)) ((sideD P o).diag (fold o I)))
          ((sideM P o).assocR (fold o F) (fold o I) (fold o I))) := by
  let S := side P o
  apply DiagonalData.cancel_left (C:=S) _ _ (join o F I) (split o F I) (split_join o F I)
  rw [tail_square,← S.assoc (join o F I),join_split,S.id_comp]

theorem twoCuts_denote {F D I R : List (NormalForm P)} {C : NormalForm P}
    (g : G P (C::C::F) D) (h : G P I (C::R)) :
    ofTerm (G.cut h (G.cut h g)).denote =
      comp (ofTerm (append .conj (F++I) I).invTerm)
        (comp (tensor .conj (ofTerm (append .conj F I).invTerm) (id (ante I)))
          (comp (splice (ofTerm h.denote)
            (comp (assocR .conj C (ante F) (ante I)) (splice (ofTerm h.denote) (ofTerm g.denote))))
            (comp (tensor .disj (ofTerm (append .disj D R).toTerm) (id (succ R)))
              (ofTerm (append .disj (D++R) R).toTerm)))) := by
  rw [cut_splice,cut_splice]
  have hc : ofTerm (append .conj (C::F) I).invTerm =
      comp (tensor .conj (id C) (ofTerm (append .conj F I).invTerm))
        (assocR .conj C (ante F) (ante I)) := split_cons .conj C F I
  rw [hc]
  simp only [Laws.assoc]
  rw [Splice.context,← Laws.assoc (assocR .conj C (ante F) (ante I)),Splice.output]
  simp only [Laws.assoc]
  rfl

theorem repair_denote {F D I R : List (NormalForm P)} {C : NormalForm P}
    (g : G P (C::C::F) D) (h : G P I (C::R)) :
    ofTerm (repair (G.cut h (G.cut h g))).denote =
      comp (ofTerm (append .conj F I).invTerm)
        (comp (tensor .conj (id (ante F)) (diag (ante I)))
          (comp (assocR .conj (ante F) (ante I) (ante I))
            (comp (splice (ofTerm h.denote)
              (comp (assocR .conj C (ante F) (ante I)) (splice (ofTerm h.denote) (ofTerm g.denote))))
              (comp (assocL .disj (succ D) (succ R) (succ R))
                (comp (tensor .disj (id (succ D)) (codiag (succ R)))
                  (ofTerm (append .disj D R).toTerm)))))) := by
  have hi := tail_decoded .conj F I
  have ho := tail_decoded .disj D R
  dsimp only [side,sideM,sideD,conjMonoidal,disjMonoidal,disjDiagonal,conjDiagonal,
    opposite,category,split] at hi ho
  simp only [Laws.assoc] at ho
  rw [repair,StructuralProgram.left_denote,StructuralProgram.right_denote,
    Route.program_arrow,Route.program_arrow,twoCuts_denote]
  simp only [Laws.assoc]
  erw [ho]
  erw [← Laws.assoc ((tailRoute F I).sideArrow .conj),
    ← Laws.assoc (comp ((tailRoute F I).sideArrow .conj) (ofTerm (append .conj (F++I) I).invTerm)),
    Laws.assoc ((tailRoute F I).sideArrow .conj),hi]
  simp only [Laws.assoc]

theorem headParent_equation {F D I R : List (NormalForm P)} {C : NormalForm P}
    (g : G P (C::C::F) D) (h : G P I (C::R)) :
    ofTerm (G.cut h (headParent g)).denote = ofTerm (repair (G.cut h (G.cut h g))).denote := by
  rw [cut_splice,headParent_denote,ContractionSplice.binary,repair_denote]
  simp only [Laws.assoc]

end DosenPetric.Reduced.Gentzen.SequentialRepair
