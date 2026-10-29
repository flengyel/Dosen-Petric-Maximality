module

public import DosenPetric.GentzenSequentialThreeFibers

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialDisjBoth
universe u
variable {P : Type u}

def move (C : NormalForm P) (Y : List (NormalForm P)) :
    ExchangeScript P (C::C::Y) (C::(Y++[C])) :=
  (BinaryMix.swapWhole Y [C]).consFixed C

theorem moveFiber (C : NormalForm P) (Y : List (NormalForm P)) :
    (move C Y).structural.route.SingleFiber (.here C (C::Y)) (.here C (Y++[C])) :=
  ExchangeScript.structural_singleFiber _ _ _ (ExchangeScript.consFixed_here C _)

def moveResidual (C : NormalForm P) (Y : List (NormalForm P)) :
    StructuralProgram P (C::Y) (Y++[C]) :=
  (move C Y).structural.residual _ _ (moveFiber C Y)

theorem moveResidual_fiber (C : NormalForm P) (Y : List (NormalForm P)) :
    (moveResidual C Y).route.SingleFiber (.here C Y) (At.shift Y (.here C [])) := by
  apply StructuralProgram.residual_singleFiber
  apply ExchangeScript.structural_singleFiber
  change (move C Y).get (.there (At.shift Y (.here C []))) = .there (.here C Y)
  rw [move,ExchangeScript.consFixed_there,BinaryMix.swapWhole_shift]
  rfl

def inputProgram {Y F H : List (NormalForm P)} (C : NormalForm P)
    (p : Route Y F) (q : Route Y H) (I : List (NormalForm P)) :
    StructuralProgram P (C::(Y++I)) (C::((F++I)++(H++I))) :=
  ((moveResidual C Y).suffixFixed I).seq
    ((BlockedLeftDisj.terminalExchange Y C I).structural.seq
      (((BlockedMix.inputRoute q p I).parallel (Route.identity [C])).program.seq
        (BinaryMix.swapWhole ((F++I)++(H++I)) [C]).inverse.structural))

theorem input_fiber {Y F H : List (NormalForm P)} (C : NormalForm P)
    (p : Route Y F) (q : Route Y H) (I : List (NormalForm P)) :
    (inputProgram C p q I).route.SingleFiber (.here C (Y++I)) (.here C ((F++I)++(H++I))) := by
  apply StructuralProgram.seq_singleFiber _ _ _ ((At.shift Y (.here C [])).before I) _
    (StructuralProgram.suffixFixed_singleFiber _ _ _ (moveResidual_fiber C Y) I)
  apply StructuralProgram.seq_singleFiber _ _ _ (At.shift (Y++I) (.here C [])) _
    (ExchangeScript.structural_singleFiber _ _ _ (BlockedLeftDisj.terminalExchange_last Y C I))
  apply StructuralProgram.seq_singleFiber _ _ _ (At.shift ((F++I)++(H++I)) (.here C [])) _
  · constructor
    · rw [StructuralProgram.route_get,Route.program_get]
      exact (Route.parallel_last_singleFiber (BlockedMix.inputRoute q p I) C).1
    · intro E b hb
      rw [StructuralProgram.route_get,Route.program_get] at hb
      exact (Route.parallel_last_singleFiber (BlockedMix.inputRoute q p I) C).2 b hb
  · apply ExchangeScript.structural_singleFiber
    apply At.index_injective
    have he := (BinaryMix.swapWhole ((F++I)++(H++I)) [C]).inverse_get
      (At.shift ((F++I)++(H++I)) (.here C []))
    rw [BinaryMix.swapWhole_shift] at he
    exact congrArg At.index he

def body {Y F H D E : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y F) (q : Route Y H)
    (f : G P (.disj A B::(F++[A])) D) (g : G P (.disj A B::(H++[B])) E) :
    G P (.disj A B::.disj A B::Y) (D++E) :=
  (move (.disj A B) Y).left (BlockedLeftDisj.headParent p q f g)

def parent {Y F H D E : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y F) (q : Route Y H)
    (f : G P (.disj A B::(F++[A])) D) (g : G P (.disj A B::(H++[B])) E) :
    G P (.disj A B::Y) (D++E) := SequentialRepair.headParent (body p q f g)

def childResult {F D I R : List (NormalForm P)} (A : NormalForm P)
    (k : G P ((F++[A])++I) (D++R)) : G P (A::(F++I)) (D++R) :=
  BlockedSource.headL A ((BlockedLeftDisj.terminalExchange F A I).inverse.left k)

def fresh {F H D E I R : List (NormalForm P)} {A B : NormalForm P}
    (k : G P ((F++[A])++I) (D++R)) (l : G P ((H++[B])++I) (E++R)) :
    G P (.disj A B::((F++I)++(H++I))) ((D++R)++(E++R)) :=
  G.disjL (childResult A k) (childResult B l)

def adapted {Y F H D E I R : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y F) (q : Route Y H)
    (k : G P ((F++[A])++I) (D++R)) (l : G P ((H++[B])++I) (E++R)) :
    G P (.disj A B::(Y++I)) ((D++E)++R) :=
  (BlockedMix.outputRoute E D R).program.right ((inputProgram (.disj A B) p q I).left (fresh k l))

theorem first_equation {Y F H D E I R : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y F) (q : Route Y H) (h : G P I (.disj A B::R))
    (f : G P (.disj A B::(F++[A])) D) (g : G P (.disj A B::(H++[B])) E) :
    ofTerm (G.cut h (body p q f g)).denote =
      ofTerm (adapted p q (G.cut h f) (G.cut h g)).denote := by
  have he := CutCommutation.same_left (move (.disj A B) Y).structural _ _ (moveFiber (.disj A B) Y)
    h (.here (.disj A B) R) (BlockedLeftDisj.headParent p q f g)
  simp only [ExchangeScript.structural_left,PositionalCut.head] at he
  apply he.trans
  rw [StructuralProgram.left_denote,BlockedLeftDisj.headParent_equation]
  simp only [adapted,inputProgram,StructuralProgram.right_denote,StructuralProgram.left_denote,
    StructuralProgram.arrow,ExchangeScript.structural_arrow,BlockedLeftDisj.parallel,
    ExchangeScript.left_denote,StructuralProgram.left_denote,StructuralProgram.right_denote,
    BlockedSource.disjLLast_eq,BlockedSource.tailL_script,ExchangeScript.left_denote,
    fresh,childResult,BlockedSource.headL_script,moveResidual,side,category,Laws.assoc]

end DosenPetric.Reduced.Gentzen.SequentialDisjBoth
