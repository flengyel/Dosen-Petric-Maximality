module

public import DosenPetric.GentzenTerminalContractionFactor

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialAdapters
universe u
variable {P : Type u}

def leftResult {F U D E I R : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (x : At F C) (y : At U C) (hp : p.route.SingleFiber x y)
    (q : StructuralProgram P D E) (k : G P (y.erase++I) (E++R)) : G P (x.erase++I) (D++R) :=
  (q.suffixFixed R).right (((p.residual x y hp).suffixFixed I).left k)

theorem leftResult_count {F U D E I R : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (x : At F C) (y : At U C) (hp : p.route.SingleFiber x y)
    (q : StructuralProgram P D E) (k : G P (y.erase++I) (E++R)) :
    (leftResult p x y hp q k).cutCount = k.cutCount := by
  rw [leftResult,StructuralProgram.right_count,StructuralProgram.left_count]

theorem leftResult_congr {F U D E I R : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (x : At F C) (y : At U C) (hp : p.route.SingleFiber x y)
    (q : StructuralProgram P D E) (k k' : G P (y.erase++I) (E++R))
    (he : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (leftResult p x y hp q k).denote = ofTerm (leftResult p x y hp q k').denote := by
  simp only [leftResult,StructuralProgram.right_denote,StructuralProgram.left_denote,he]

theorem left_equation {F U D E I J : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (x : At F C) (y : At U C) (hp : p.route.SingleFiber x y)
    (q : StructuralProgram P D E) (h : G P I J) (z : At J C) (g : G P U E) :
    ofTerm (PositionalCut.cut h z (q.right (p.left g)) x).denote =
      ofTerm (leftResult p x y hp q (PositionalCut.cut h z g y)).denote := by
  apply (CutCommutation.selected_opposite_right q h z (p.left g) x).trans
  rw [leftResult,StructuralProgram.right_denote,StructuralProgram.right_denote]
  exact congrArg (fun k => comp k _) (CutCommutation.same_left p x y hp h z g)

end DosenPetric.Reduced.Gentzen.SequentialAdapters
