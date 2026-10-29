module

public import DosenPetric.GentzenSequentialCutDenotation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialConjunction
universe u
variable {P : Type u}

def body {F D : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (.conj A B::A::B::F) D) : G P (.conj A B::.conj A B::F) D :=
  G.conjL [.conj A B] F D A B f

def parent {F D : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (.conj A B::A::B::F) D) : G P (.conj A B::F) D :=
  SequentialRepair.headParent (body f)

def fresh {F D I R : List (NormalForm P)} {A B : NormalForm P}
    (k : G P ((A::B::F)++I) (D++R)) : G P (.conj A B::(F++I)) (D++R) :=
  G.conjL [] (F++I) (D++R) A B k

theorem first_equation {F D I R : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (.conj A B::A::B::F) D) (h : G P I (.conj A B::R)) :
    ofTerm (G.cut h (body f)).denote = ofTerm (fresh (G.cut h f)).denote := by
  have he := CutCommutation.same_conjL_before h (.here (.conj A B) R) f (.here (.conj A B) [])
  change ofTerm (G.cut h (body f)).denote = ofTerm (fresh (G.cut h f)).denote at he
  exact he

theorem native_equation {F D I R : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (.conj A B::A::B::F) D) (h : G P I (.conj A B::R)) :
    ofTerm (G.cut h (parent f)).denote =
      ofTerm (SequentialRepair.repair (G.cut h (fresh (G.cut h f)))).denote := by
  apply (SequentialRepair.headParent_equation (body f) h).trans
  apply SequentialRepair.repair_congr
  exact Rules.cut_congr rfl (first_equation f h)

end DosenPetric.Reduced.Gentzen.SequentialConjunction
