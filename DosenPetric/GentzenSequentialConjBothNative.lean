module

public import DosenPetric.GentzenBlockedConjSecondRank

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialConjBoth
universe u
variable {P : Type u}

def parent {Γ Θ D E Y : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (f : G P Γ (A::.conj A B::D)) (g : G P Θ (B::.conj A B::E)) :
    G P (Γ++Θ) (.conj A B::Y) :=
  SequentialRepair.headParentRight (BlockedRightConj.headParent p q f g)

def child {Γ D : List (NormalForm P)} (A C : NormalForm P) (f : G P Γ (A::C::D)) :
    G P Γ (C::A::D) := (HeadRouting.front [A] D C).right f

def fresh {Γ Θ D E I J : List (NormalForm P)} {A B : NormalForm P}
    (k : G P (I++Γ) (J++A::D)) (l : G P (I++Θ) (J++B::E)) :
    G P ((I++Γ)++(I++Θ)) (.conj A B::((J++D)++(J++E))) :=
  G.conjR ((HeadRouting.front J D A).right k) ((HeadRouting.front J E B).right l)

def adapted {Γ Θ D E Y I J : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (k : G P (I++Γ) (J++A::D)) (l : G P (I++Θ) (J++B::E)) :
    G P (I++(Γ++Θ)) (.conj A B::(J++Y)) :=
  ((BlockedMix.rightOutputRoute q p J).head (.conj A B)).program.right
    ((BlockedMix.rightInputRoute I Γ Θ).program.left (fresh k l))

theorem first_equation {Γ Θ D E Y I J : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (f : G P Γ (A::.conj A B::D)) (g : G P Θ (B::.conj A B::E)) (h : G P (.conj A B::I) J) :
    ofTerm ((HeadRouting.front J Y (.conj A B)).right
      (G.cut (BlockedRightConj.headParent p q f g) h)).denote =
      ofTerm (adapted p q (G.cut (child A (.conj A B) f) h) (G.cut (child B (.conj A B) g) h)).denote := by
  rw [ExchangeScript.right_denote,BlockedRightConj.headParent_equation,BlockedRightConj.parallel,
    ExchangeScript.right_denote]
  have hc := (HeadRouting.front J Y (.conj A B)).arrow_inverse .disj
  change comp ((HeadRouting.front J Y (.conj A B)).inverse.arrow .disj)
    ((HeadRouting.front J Y (.conj A B)).arrow .disj) = id _ at hc
  rw [Laws.assoc]
  erw [hc]
  erw [Laws.comp_id]
  simp only [adapted,StructuralProgram.left_denote,StructuralProgram.right_denote,Laws.assoc]
  rfl

def rebuild {Γ Θ D E Y I J : List (NormalForm P)} (C : NormalForm P)
    (p : Route Y D) (q : Route Y E)
    (l : G P (I++((I++Γ)++(I++Θ))) (J++((J++D)++(J++E)))) :
    G P (I++(Γ++Θ)) (J++Y) :=
  SequentialRepair.prefixRepair
    (SequentialAdapters.rightResult (BlockedMix.rightInputRoute I Γ Θ).program
      ((BlockedMix.rightOutputRoute q p J).head C).program
      (.here C (J++Y)) (.here C ((J++D)++(J++E)))
      ((BlockedMix.rightOutputRoute q p J).head_singleFiber C) l)

theorem rebuild_count {Γ Θ D E Y I J : List (NormalForm P)} (C : NormalForm P)
    (p : Route Y D) (q : Route Y E)
    (l : G P (I++((I++Γ)++(I++Θ))) (J++((J++D)++(J++E)))) :
    (rebuild C p q l).cutCount = l.cutCount := by
  rw [rebuild,SequentialRepair.prefixRepair_count,SequentialAdapters.rightResult_count]

theorem rebuild_congr {Γ Θ D E Y I J : List (NormalForm P)} (C : NormalForm P)
    (p : Route Y D) (q : Route Y E)
    (l l' : G P (I++((I++Γ)++(I++Θ))) (J++((J++D)++(J++E))))
    (he : ofTerm l.denote = ofTerm l'.denote) :
    ofTerm (rebuild C p q l).denote = ofTerm (rebuild C p q l').denote :=
  SequentialRepair.prefixRepair_congr _ _ (SequentialAdapters.rightResult_congr _ _ _ _ _ _ _ he)

theorem native_equation {Γ Θ D E Y I J : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (f : G P Γ (A::.conj A B::D)) (g : G P Θ (B::.conj A B::E)) (h : G P (.conj A B::I) J) :
    ofTerm (G.cut (parent p q f g) h).denote =
      ofTerm (rebuild (.conj A B) p q
        (G.cut (fresh (G.cut (child A (.conj A B) f) h) (G.cut (child B (.conj A B) g) h)) h)).denote := by
  apply (SequentialRepair.headParentRight_equation (BlockedRightConj.headParent p q f g) h).trans
  have he : ofTerm (SequentialRepair.rightTwoCuts (BlockedRightConj.headParent p q f g) h).denote =
      ofTerm (G.cut (adapted p q (G.cut (child A (.conj A B) f) h) (G.cut (child B (.conj A B) g) h)) h).denote :=
    Rules.cut_congr (first_equation p q f g h) (g:=h.denote) rfl
  apply (SequentialRepair.prefixRepair_congr _ _ he).trans
  apply SequentialRepair.prefixRepair_congr
  have he := SequentialAdapters.right_equation (BlockedMix.rightInputRoute I Γ Θ).program
    ((BlockedMix.rightOutputRoute q p J).head (.conj A B)).program _ _
    ((BlockedMix.rightOutputRoute q p J).head_singleFiber (.conj A B))
    (fresh (G.cut (child A (.conj A B) f) h) (G.cut (child B (.conj A B) g) h)) h (.here (.conj A B) I)
  simp only [PositionalCut.head] at he
  exact he

end DosenPetric.Reduced.Gentzen.SequentialConjBoth
