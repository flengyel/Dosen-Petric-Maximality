module

public import DosenPetric.GentzenSequentialDisjBothNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialDisjBoth
universe u
variable {P : Type u}

def rebuild {Y F H D E I R : List (NormalForm P)} (C : NormalForm P)
    (p : Route Y F) (q : Route Y H)
    (l : G P (((F++I)++(H++I))++I) (((D++R)++(E++R))++R)) :
    G P (Y++I) ((D++E)++R) :=
  SequentialRepair.repair
    (SequentialAdapters.leftResult (inputProgram C p q I) (.here C (Y++I))
      (.here C ((F++I)++(H++I))) (input_fiber C p q I)
      (BlockedMix.outputRoute E D R).program l)

theorem rebuild_count {Y F H D E I R : List (NormalForm P)} (C : NormalForm P)
    (p : Route Y F) (q : Route Y H)
    (l : G P (((F++I)++(H++I))++I) (((D++R)++(E++R))++R)) :
    (rebuild C p q l).cutCount = l.cutCount := by
  rw [rebuild,SequentialRepair.repair_count,SequentialAdapters.leftResult_count]

theorem rebuild_congr {Y F H D E I R : List (NormalForm P)} (C : NormalForm P)
    (p : Route Y F) (q : Route Y H)
    (l l' : G P (((F++I)++(H++I))++I) (((D++R)++(E++R))++R))
    (he : ofTerm l.denote = ofTerm l'.denote) :
    ofTerm (rebuild C p q l).denote = ofTerm (rebuild C p q l').denote :=
  SequentialRepair.repair_congr _ _ (SequentialAdapters.leftResult_congr _ _ _ _ _ _ _ he)

theorem outer_equation {Y F H D E I R : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y F) (q : Route Y H) (h : G P I (.disj A B::R))
    (k : G P ((F++[A])++I) (D++R)) (l : G P ((H++[B])++I) (E++R)) :
    ofTerm (SequentialRepair.repair (G.cut h (adapted p q k l))).denote =
      ofTerm (rebuild (.disj A B) p q (G.cut h (fresh k l))).denote := by
  apply SequentialRepair.repair_congr
  have he := SequentialAdapters.left_equation (inputProgram (.disj A B) p q I) _ _
    (input_fiber (.disj A B) p q I) (BlockedMix.outputRoute E D R).program
    h (.here (.disj A B) R) (fresh k l)
  simp only [PositionalCut.head] at he
  exact he

theorem native_equation {Y F H D E I R : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y F) (q : Route Y H) (h : G P I (.disj A B::R))
    (f : G P (.disj A B::(F++[A])) D) (g : G P (.disj A B::(H++[B])) E) :
    ofTerm (G.cut h (parent p q f g)).denote =
      ofTerm (rebuild (.disj A B) p q (G.cut h (fresh (G.cut h f) (G.cut h g)))).denote := by
  apply (SequentialRepair.headParent_equation (body p q f g) h).trans
  have he : ofTerm (G.cut h (G.cut h (body p q f g))).denote =
      ofTerm (G.cut h (adapted p q (G.cut h f) (G.cut h g))).denote :=
    Rules.cut_congr (f:=h.denote) rfl (first_equation p q h f g)
  apply (SequentialRepair.repair_congr _ _ he).trans
  exact outer_equation p q h (G.cut h f) (G.cut h g)

end DosenPetric.Reduced.Gentzen.SequentialDisjBoth
