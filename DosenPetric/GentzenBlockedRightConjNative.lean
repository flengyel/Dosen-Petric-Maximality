module

public import DosenPetric.GentzenBlockedRightConjRoutes

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedRightConj
universe u
variable {P : Type u}

def headParent {Γ Θ D E Y : List (NormalForm P)} {A B C : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (f : G P Γ (A::C::D)) (g : G P Θ (B::C::E)) :
    G P (Γ++Θ) (C::(.conj A B::Y)) :=
  (HeadRouting.front [.conj A B] Y C).right
    (((((p.head C).append (q.head C)).head (.conj A B)).program).right (G.conjR f g))

def parallel {Γ Θ D E Y T J : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (k : G P (T++Γ) (J++(A::D))) (l : G P (T++Θ) (J++(B::E))) :
    G P (T++(Γ++Θ)) (J++(.conj A B::Y)) :=
  (HeadRouting.front J Y (.conj A B)).inverse.right
    ((BlockedMix.rightInputRoute T Γ Θ).program.left
      ((((BlockedMix.rightOutputRoute q p J).head (.conj A B)).program).right
        (G.conjR ((HeadRouting.front J D A).right k) ((HeadRouting.front J E B).right l))))

theorem parallel_count {Γ Θ D E Y T J : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (k : G P (T++Γ) (J++(A::D))) (l : G P (T++Θ) (J++(B::E))) :
    (parallel p q k l).cutCount = k.cutCount+l.cutCount := by
  simp only [parallel,ExchangeScript.right_count,StructuralProgram.left_count,
    StructuralProgram.right_count,G.cutCount]

theorem headParent_denote {Γ Θ D E Y : List (NormalForm P)} {A B C : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (f : G P Γ (A::C::D)) (g : G P Θ (B::C::E)) :
    ofTerm (headParent p q f g).denote =
      comp (ofTerm (append .conj Γ Θ).invTerm)
        (sharedParent (p.sideArrow .disj) (q.sideArrow .disj) (ofTerm f.denote) (ofTerm g.denote)) := by
  rw [headParent,ExchangeScript.right_denote,StructuralProgram.right_denote,Route.program_arrow,
    Route.head_side,HeadRouting.front_singleton,G.denote_conjR]
  have he := Route.append_split .disj (p.head C) (q.head C)
  rw [Route.head_side,Route.head_side] at he
  dsimp only [side,sideD,sideM,disjMonoidal,opposite,category,split,disjDiagonal,DiagonalData.pair] at he ⊢
  simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id,Laws.assoc]
  rw [← Laws.assoc (tensor .disj (id (.conj A B)) (ofTerm (append .disj (C::D) (C::E)).toTerm)),
    Laws.tensor_comp,Laws.id_comp]
  erw [he]
  rfl

theorem child_denote {Γ D T J : List (NormalForm P)} {A C : NormalForm P}
    (f : G P Γ (A::C::D)) (h : G P (C::T) J) :
    ofTerm ((HeadRouting.front J D A).right
      (G.cut ((HeadRouting.front [A] D C).right f) h)).denote =
      comp (ofTerm (append .conj T Γ).invTerm)
        (comp (DoubleConjSplice.child (ofTerm f.denote) (ofTerm h.denote))
          (tensor .disj (id A) (ofTerm (append .disj J D).toTerm))) := by
  rw [ExchangeScript.right_denote,cut_splice,ExchangeScript.right_denote,HeadRouting.front_singleton]
  simp only [Laws.assoc]
  have he := HeadRouting.front_split .disj J D A
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at he
  erw [he]
  simp only [DoubleConjSplice.child,Laws.assoc]
  rfl

end DosenPetric.Reduced.Gentzen.BlockedRightConj
