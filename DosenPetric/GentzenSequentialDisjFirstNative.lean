module

public import DosenPetric.GentzenExchangeStructuralProofs
public import DosenPetric.GentzenDisjRightFirstSelected

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialDisjFirst
universe u
variable {P : Type u}

def body {F U D E : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::.disj A B::F) D) (g : G P (B::U) E) :
    G P (.disj A B::.disj A B::(F++U)) (D++E) :=
  (HeadRouting.front [.disj A B] (F++U) (.disj A B)).left
    (G.disjL (Γ:=.disj A B::F) (Θ:=U) f g)

def parent {F U D E : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::.disj A B::F) D) (g : G P (B::U) E) : G P (.disj A B::(F++U)) (D++E) :=
  SequentialRepair.headParent (body f g)

def child {F D : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::.disj A B::F) D) : G P (.disj A B::A::F) D :=
  (HeadRouting.front [A] F (.disj A B)).left f

def fresh {F U D E I R : List (NormalForm P)} {A B : NormalForm P}
    (k : G P (A::(F++I)) (D++R)) (g : G P (B::U) E) :
    G P (.disj A B::((F++I)++U)) ((D++R)++E) := G.disjL k g

def inputScript (C : NormalForm P) (F U I : List (NormalForm P)) :
    ExchangeScript P (C::((F++U)++I)) (C::((F++I)++U)) :=
  BinaryLogical.lastExchange (C::F) I U

theorem input_head (C : NormalForm P) (F U I : List (NormalForm P)) :
    (inputScript C F U I).get (.here C ((F++I)++U)) = .here C ((F++U)++I) := by
  change ((BinaryLogical.lastExchange F I U).consFixed C).get (.here C ((F++I)++U)) = _
  rw [ExchangeScript.consFixed_here]

def adapter {F U D E I R : List (NormalForm P)} (C : NormalForm P)
    (l : G P (((F++I)++U)++I) (((D++R)++E)++R)) :
    G P (((F++U)++I)++I) (((D++E)++R)++R) :=
  SequentialAdapters.leftResult (inputScript C F U I).structural
    (.here C ((F++U)++I)) (.here C ((F++I)++U))
    (ExchangeScript.structural_singleFiber _ _ _ (input_head C F U I))
    (BinaryLogical.lastExchange D R E).structural l

theorem adapter_count {F U D E I R : List (NormalForm P)} (C : NormalForm P)
    (l : G P (((F++I)++U)++I) (((D++R)++E)++R)) : (adapter C l).cutCount = l.cutCount := by
  rw [adapter,SequentialAdapters.leftResult_count]

theorem adapter_congr {F U D E I R : List (NormalForm P)} (C : NormalForm P)
    (l l' : G P (((F++I)++U)++I) (((D++R)++E)++R)) (he : ofTerm l.denote = ofTerm l'.denote) :
    ofTerm (adapter C l).denote = ofTerm (adapter C l').denote := by
  exact SequentialAdapters.leftResult_congr _ _ _ _ _ _ _ he

theorem first_equation {F U D E I R : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::.disj A B::F) D) (g : G P (B::U) E) (h : G P I (.disj A B::R)) :
    ofTerm (G.cut h (body f g)).denote =
      ofTerm (DisjLogical.disjRightFirstNative (G.cut h (child f)) g).denote :=
  DisjLogical.disjRightFirstNative_equation f g h

theorem outer_equation {F U D E I R : List (NormalForm P)} {A B : NormalForm P}
    (k : G P (A::(F++I)) (D++R)) (g : G P (B::U) E) (h : G P I (.disj A B::R)) :
    ofTerm (G.cut h (DisjLogical.disjRightFirstNative k g)).denote =
      ofTerm (adapter (.disj A B) (G.cut h (fresh k g))).denote := by
  have he := SequentialAdapters.left_equation (inputScript (.disj A B) F U I).structural
    (.here (.disj A B) ((F++U)++I)) (.here (.disj A B) ((F++I)++U))
    (ExchangeScript.structural_singleFiber _ _ _ (input_head (.disj A B) F U I))
    (BinaryLogical.lastExchange D R E).structural h (.here (.disj A B) R) (fresh k g)
  simp only [ExchangeScript.structural_left,ExchangeScript.structural_right,PositionalCut.head] at he
  exact he

theorem native_equation {F U D E I R : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::.disj A B::F) D) (g : G P (B::U) E) (h : G P I (.disj A B::R)) :
    ofTerm (G.cut h (parent f g)).denote =
      ofTerm (SequentialRepair.repair (adapter (.disj A B) (G.cut h (fresh (G.cut h (child f)) g)))).denote := by
  apply (SequentialRepair.headParent_equation (body f g) h).trans
  apply SequentialRepair.repair_congr
  apply (Rules.cut_congr rfl (first_equation f g h)).trans
  exact outer_equation (G.cut h (child f)) g h

end DosenPetric.Reduced.Gentzen.SequentialDisjFirst
