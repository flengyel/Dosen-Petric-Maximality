module

public import DosenPetric.GentzenTerminalSelectedFolds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedLeftDisj
universe u
variable {P : Type u}

def terminalExchange (F : List (NormalForm P)) (A : NormalForm P) (I : List (NormalForm P)) :
    ExchangeScript P ((F++[A])++I) ((F++I)++[A]) :=
  (ExchangeScript.exchange F I [A] []).reindex (by rw [List.append_nil]) (by rw [List.append_nil])

def headParent {Y F H D E : List (NormalForm P)} {A B C : NormalForm P}
    (p : Route Y F) (q : Route Y H)
    (f : G P (C::(F++[A])) D) (g : G P (C::(H++[B])) E) :
    G P (C::(Y++[.disj A B])) (D++E) :=
  ((((p.head C).append (q.head C)).parallel (Route.identity [.disj A B])).program).left
    (BlockedSource.disjLLast f g)

def parallel {Y F H D E I R : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y F) (q : Route Y H)
    (k : G P ((F++[A])++I) (D++R)) (l : G P ((H++[B])++I) (E++R)) :
    G P ((Y++[.disj A B])++I) ((D++E)++R) :=
  (terminalExchange Y (.disj A B) I).left
    ((((BlockedMix.inputRoute q p I).parallel (Route.identity [.disj A B])).program).left
      ((BlockedMix.outputRoute E D R).program.right
        (BlockedSource.disjLLast
          ((terminalExchange F A I).inverse.left k)
          ((terminalExchange H B I).inverse.left l))))

theorem parallel_count {Y F H D E I R : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y F) (q : Route Y H)
    (k : G P ((F++[A])++I) (D++R)) (l : G P ((H++[B])++I) (E++R)) :
    (parallel p q k l).cutCount = k.cutCount+l.cutCount := by
  simp only [parallel,ExchangeScript.left_count,StructuralProgram.left_count,
    StructuralProgram.right_count,BlockedSource.disjLLast_count]

def childArrow {F D : List (NormalForm P)} {C A : NormalForm P}
    (f : G P (C::(F++[A])) D) : Hom (.conj C (.conj (ante F) A)) (succ D) :=
  comp (tensor .conj (id C) (TerminalFold.into F A)) (ofTerm f.denote)

end DosenPetric.Reduced.Gentzen.BlockedLeftDisj
