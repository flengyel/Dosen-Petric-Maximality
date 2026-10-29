module

public import DosenPetric.GentzenAppendixCFreshRight
public import DosenPetric.GentzenDisjRightSecondSelected

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialDisjSecond
universe u
variable {P : Type u}

def body {F U D E : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::F) D) (g : G P (B::.disj A B::U) E) :
    G P (.disj A B::.disj A B::(F++U)) (D++E) :=
  (HeadRouting.front (.disj A B::F) U (.disj A B)).left
    (G.disjL (Γ:=F) (Θ:=.disj A B::U) f g)

def parent {F U D E : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::F) D) (g : G P (B::.disj A B::U) E) : G P (.disj A B::(F++U)) (D++E) :=
  SequentialRepair.headParent (body f g)

def child {U E : List (NormalForm P)} {A B : NormalForm P}
    (g : G P (B::.disj A B::U) E) : G P (.disj A B::B::U) E :=
  (HeadRouting.front [B] U (.disj A B)).left g

def fresh {F U D E I R : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::F) D) (k : G P (B::(U++I)) (E++R)) :
    G P (.disj A B::(F++(U++I))) (D++(E++R)) := G.disjL f k

def inputScript (C : NormalForm P) (F U I : List (NormalForm P)) :
    ExchangeScript P (C::((F++U)++I)) (C::(F++(U++I))) :=
  (ExchangeScript.appendAssoc F U I).inverse.consFixed C

theorem input_head (C : NormalForm P) (F U I : List (NormalForm P)) :
    (inputScript C F U I).get (.here C (F++(U++I))) = .here C ((F++U)++I) :=
  ExchangeScript.consFixed_here C _

def adapter {F U D E I R : List (NormalForm P)} (C : NormalForm P)
    (l : G P ((F++(U++I))++I) ((D++(E++R))++R)) :
    G P (((F++U)++I)++I) (((D++E)++R)++R) :=
  SequentialAdapters.leftResult (inputScript C F U I).structural
    (.here C ((F++U)++I)) (.here C (F++(U++I)))
    (ExchangeScript.structural_singleFiber _ _ _ (input_head C F U I))
    (ExchangeScript.appendAssoc D E R).inverse.structural l

theorem adapter_count {F U D E I R : List (NormalForm P)} (C : NormalForm P)
    (l : G P ((F++(U++I))++I) ((D++(E++R))++R)) : (adapter C l).cutCount = l.cutCount := by
  rw [adapter,SequentialAdapters.leftResult_count]

theorem adapter_congr {F U D E I R : List (NormalForm P)} (C : NormalForm P)
    (l l' : G P ((F++(U++I))++I) ((D++(E++R))++R)) (he : ofTerm l.denote = ofTerm l'.denote) :
    ofTerm (adapter C l).denote = ofTerm (adapter C l').denote :=
  SequentialAdapters.leftResult_congr _ _ _ _ _ _ _ he

theorem first_equation {F U D E I R : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::F) D) (g : G P (B::.disj A B::U) E) (h : G P I (.disj A B::R)) :
    ofTerm (G.cut h (body f g)).denote =
      ofTerm (DisjLogical.disjRightSecondNative f (G.cut h (child g))).denote :=
  DisjLogical.disjRightSecondNative_equation f g h

theorem outer_equation {F U D E I R : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::F) D) (k : G P (B::(U++I)) (E++R)) (h : G P I (.disj A B::R)) :
    ofTerm (G.cut h (DisjLogical.disjRightSecondNative f k)).denote =
      ofTerm (adapter (.disj A B) (G.cut h (fresh f k))).denote := by
  have he := SequentialAdapters.left_equation (inputScript (.disj A B) F U I).structural
    (.here (.disj A B) ((F++U)++I)) (.here (.disj A B) (F++(U++I)))
    (ExchangeScript.structural_singleFiber _ _ _ (input_head (.disj A B) F U I))
    (ExchangeScript.appendAssoc D E R).inverse.structural h (.here (.disj A B) R) (fresh f k)
  simp only [ExchangeScript.structural_left,ExchangeScript.structural_right,PositionalCut.head] at he
  exact he

theorem native_equation {F U D E I R : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::F) D) (g : G P (B::.disj A B::U) E) (h : G P I (.disj A B::R)) :
    ofTerm (G.cut h (parent f g)).denote =
      ofTerm (SequentialRepair.repair (adapter (.disj A B) (G.cut h (fresh f (G.cut h (child g)))))).denote := by
  apply (SequentialRepair.headParent_equation (body f g) h).trans
  apply SequentialRepair.repair_congr
  apply (Rules.cut_congr rfl (first_equation f g h)).trans
  exact outer_equation f (G.cut h (child g)) h

end DosenPetric.Reduced.Gentzen.SequentialDisjSecond
