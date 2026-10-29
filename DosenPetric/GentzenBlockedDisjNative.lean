module

public import DosenPetric.GentzenBlockedDisjInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedDisj
universe u
variable {P : Type u}

def headParent {F U D E Y : List (NormalForm P)} {A B C : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (f : G P (F++[A]) (C::D)) (g : G P (U++[B]) (C::E)) :
    G P ((F++U)++[.disj A B]) (C::Y) :=
  ((p.head C).append (q.head C)).program.right (BlockedSource.disjLLast f g)

def parallel {F U D E Y T J : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (k : G P (T++(F++[A])) (J++D)) (l : G P (T++(U++[B])) (J++E)) :
    G P (T++((F++U)++[.disj A B])) (J++Y) :=
  (parallelInput T F U (.disj A B)).left
    ((BlockedMix.rightOutputRoute q p J).program.right
      (BlockedSource.disjLLast
        ((ExchangeScript.appendAssoc T F [A]).inverse.left k)
        ((ExchangeScript.appendAssoc T U [B]).inverse.left l)))

theorem headParent_denote {F U D E Y : List (NormalForm P)} {A B C : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (f : G P (F++[A]) (C::D)) (g : G P (U++[B]) (C::E)) :
    ofTerm (headParent p q f g).denote =
      comp (TerminalFold.sourceInput F U (.disj A B))
        (headRightParent (p.sideArrow .disj) (q.sideArrow .disj)
          (comp (TerminalFold.into F A) (ofTerm f.denote))
          (comp (TerminalFold.into U B) (ofTerm g.denote))) := by
  rw [headParent,StructuralProgram.right_denote,Route.program_arrow,TerminalFold.disjLLast_denote]
  have he := Route.append_split .disj (p.head C) (q.head C)
  rw [Route.head_side,Route.head_side] at he
  dsimp only [side,sideD,sideM,disjMonoidal,opposite,category,split,disjDiagonal,DiagonalData.pair] at he
  simp only [Laws.assoc]
  erw [he]
  rfl

theorem parallel_count {F U D E Y T J : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (k : G P (T++(F++[A])) (J++D)) (l : G P (T++(U++[B])) (J++E)) :
    (parallel p q k l).cutCount = k.cutCount+l.cutCount := by
  simp only [parallel,StructuralProgram.left_count,StructuralProgram.right_count,
    BlockedSource.disjLLast_count,ExchangeScript.left_count]

theorem child_cut_denote {F D T J : List (NormalForm P)} {A C : NormalForm P}
    (f : G P (F++[A]) (C::D)) (h : G P (C::T) J) :
    comp (tensor .conj (ofTerm (append .conj T F).toTerm) (id A))
      (comp (TerminalFold.into (T++F) A)
        (ofTerm ((ExchangeScript.appendAssoc T F [A]).inverse.left (G.cut f h)).denote)) =
      comp (assocL .conj (ante T) (ante F) A)
        (comp (splice (comp (TerminalFold.into F A) (ofTerm f.denote)) (ofTerm h.denote))
          (ofTerm (append .disj J D).toTerm)) := by
  rw [ExchangeScript.left_denote,cut_splice]
  rw [← Laws.assoc (tensor .conj (ofTerm (append .conj T F).toTerm) (id A)),
    ← Laws.assoc (comp (tensor .conj (ofTerm (append .conj T F).toTerm) (id A))
      (TerminalFold.into (T++F) A)),
    ← Laws.assoc (comp (comp (tensor .conj (ofTerm (append .conj T F).toTerm) (id A))
      (TerminalFold.into (T++F) A)) ((ExchangeScript.appendAssoc T F [A]).inverse.arrow .conj))]
  have he := TerminalFold.child_into T F A
  simp only [← Laws.assoc] at he
  erw [he]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id (ante T)) (TerminalFold.into F A)),← Splice.input]

theorem sourceConj_split {T F U : List (NormalForm P)} {A B D E : NormalForm P}
    (f : Hom (.conj (ante (T++F)) A) D) (g : Hom (.conj (ante (T++U)) B) E) :
    comp (ofTerm (Rules.sourceConj (ante (T++F)) (ante (T++U)) A B)) (tensor .disj f g) =
      comp (tensor .conj
        (tensor .conj (ofTerm (append .conj T F).invTerm) (ofTerm (append .conj T U).invTerm))
        (id (.disj A B)))
        (comp (ofTerm (Rules.sourceConj (.conj (ante T) (ante F)) (.conj (ante T) (ante U)) A B))
          (tensor .disj
            (comp (tensor .conj (ofTerm (append .conj T F).toTerm) (id A)) f)
            (comp (tensor .conj (ofTerm (append .conj T U).toTerm) (id B)) g))) := by
  have hn := sourceConj_nat (ofTerm (append .conj T F).invTerm)
    (ofTerm (append .conj T U).invTerm) (id A) (id B)
  rw [Laws.tensor_id] at hn
  have he := congrArg (fun v => comp v (tensor .disj
    (comp (tensor .conj (ofTerm (append .conj T F).toTerm) (id A)) f)
    (comp (tensor .conj (ofTerm (append .conj T U).toTerm) (id B)) g))) hn
  have hf : comp (tensor .conj (ofTerm (append .conj T F).invTerm) (id A))
      (comp (tensor .conj (ofTerm (append .conj T F).toTerm) (id A)) f) = f := by
    rw [← Laws.assoc,Laws.tensor_comp,(append .conj T F).inv_to,Laws.id_comp,Laws.tensor_id,Laws.id_comp]
  have hg : comp (tensor .conj (ofTerm (append .conj T U).invTerm) (id B))
      (comp (tensor .conj (ofTerm (append .conj T U).toTerm) (id B)) g) = g := by
    rw [← Laws.assoc,Laws.tensor_comp,(append .conj T U).inv_to,Laws.id_comp,Laws.tensor_id,Laws.id_comp]
  simp only [Laws.assoc] at he
  rw [Laws.tensor_comp,hf,hg] at he
  exact he

end DosenPetric.Reduced.Gentzen.BlockedDisj
