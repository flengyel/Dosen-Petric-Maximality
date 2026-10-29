module

public import DosenPetric.GentzenSequentialCoproductHead

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialRepair
universe u
variable {P : Type u}

def rightTwoCuts {F D I J : List (NormalForm P)} {C : NormalForm P}
    (g : G P F (C::C::D)) (h : G P (C::I) J) : G P (I++(I++F)) (J++(J++D)) :=
  G.cut ((HeadRouting.front J D C).right (G.cut g h)) h

theorem rightTwoCuts_denote {F D I J : List (NormalForm P)} {C : NormalForm P}
    (g : G P F (C::C::D)) (h : G P (C::I) J) :
    ofTerm (rightTwoCuts g h).denote =
      comp (ofTerm (append .conj I (I++F)).invTerm)
        (comp (tensor .conj (id (ante I)) (ofTerm (append .conj I F).invTerm))
          (comp (splice (comp (splice (ofTerm g.denote) (ofTerm h.denote))
            ((sideM P .disj).cross C (succ J) (succ D))) (ofTerm h.denote))
            (comp (tensor .disj (id (succ J)) (ofTerm (append .disj J D).toTerm))
              (ofTerm (append .disj J (J++D)).toTerm)))) := by
  rw [rightTwoCuts,cut_splice,ExchangeScript.right_denote,cut_splice]
  have hf := HeadRouting.front_split (P:=P) .disj J D C
  change comp (ofTerm (append .disj J (C::D)).toTerm) ((HeadRouting.front J D C).arrow .disj) =
    comp ((sideM P .disj).cross C (succ J) (succ D))
      (tensor .disj (id C) (ofTerm (append .disj J D).toTerm)) at hf
  simp only [Laws.assoc]
  rw [hf,← Laws.assoc (splice (ofTerm g.denote) (ofTerm h.denote)),Splice.input,Splice.residual]
  simp only [Laws.assoc]

theorem prefixRepair_rightTwoCuts_denote {F D I J : List (NormalForm P)} {C : NormalForm P}
    (g : G P F (C::C::D)) (h : G P (C::I) J) :
    ofTerm (prefixRepair (rightTwoCuts g h)).denote =
      comp (ofTerm (append .conj I F).invTerm)
        (comp (tensor .conj (diag (ante I)) (id (ante F)))
          (comp (assocL .conj (ante I) (ante I) (ante F))
            (comp (splice (comp (splice (ofTerm g.denote) (ofTerm h.denote))
              ((sideM P .disj).cross C (succ J) (succ D))) (ofTerm h.denote))
              (comp (assocR .disj (succ J) (succ J) (succ D))
                (comp (tensor .disj (codiag (succ J)) (id (succ D)))
                  (ofTerm (append .disj J D).toTerm)))))) := by
  have hi := head_decoded .conj I F
  have ho := head_decoded .disj J D
  dsimp only [side,sideM,sideD,conjMonoidal,disjMonoidal,conjDiagonal,disjDiagonal,
    opposite,category,split] at hi ho
  simp only [Laws.assoc] at ho
  rw [prefixRepair,StructuralProgram.left_denote,StructuralProgram.right_denote,
    Route.program_arrow,Route.program_arrow,rightTwoCuts_denote]
  simp only [Laws.assoc]
  erw [ho]
  erw [← Laws.assoc ((headRoute I F).sideArrow .conj),
    ← Laws.assoc (comp ((headRoute I F).sideArrow .conj) (ofTerm (append .conj I (I++F)).invTerm)),
    Laws.assoc ((headRoute I F).sideArrow .conj),hi]
  simp only [Laws.assoc]

theorem headParentRight_equation {F D I J : List (NormalForm P)} {C : NormalForm P}
    (g : G P F (C::C::D)) (h : G P (C::I) J) :
    ofTerm (G.cut (headParentRight g) h).denote = ofTerm (prefixRepair (rightTwoCuts g h)).denote := by
  rw [cut_splice,headParentRight_denote,ContractionSplice.head_right_binary,prefixRepair_rightTwoCuts_denote]
  simp only [Laws.assoc]

end DosenPetric.Reduced.Gentzen.SequentialRepair
