module

public import DosenPetric.GentzenBlockedDisjBothRank

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialAdapters
universe u
variable {P : Type u}

def rightResult {F U D E I J : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (q : StructuralProgram P D E)
    (x : At D C) (y : At E C) (hq : q.route.SingleFiber x y)
    (k : G P (I++U) (J++y.erase)) : G P (I++F) (J++x.erase) :=
  (p.prefixFixed I).left (((q.residual x y hq).prefixFixed J).right k)

theorem rightResult_count {F U D E I J : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (q : StructuralProgram P D E)
    (x : At D C) (y : At E C) (hq : q.route.SingleFiber x y)
    (k : G P (I++U) (J++y.erase)) : (rightResult p q x y hq k).cutCount = k.cutCount := by
  rw [rightResult,StructuralProgram.left_count,StructuralProgram.right_count]

theorem rightResult_congr {F U D E I J : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (q : StructuralProgram P D E)
    (x : At D C) (y : At E C) (hq : q.route.SingleFiber x y)
    (k k' : G P (I++U) (J++y.erase)) (he : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (rightResult p q x y hq k).denote = ofTerm (rightResult p q x y hq k').denote := by
  simp only [rightResult,StructuralProgram.left_denote,StructuralProgram.right_denote,he]

theorem right_equation {F U D E I J : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (q : StructuralProgram P D E)
    (x : At D C) (y : At E C) (hq : q.route.SingleFiber x y)
    (f : G P U E) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (q.right (p.left f)) x h z).denote =
      ofTerm (rightResult p q x y hq (PositionalCut.cut f y h z)).denote := by
  apply (CutCommutation.same_right q x y hq (p.left f) h z).trans
  rw [StructuralProgram.right_denote,CutCommutation.selected_opposite_left,
    StructuralProgram.left_denote,rightResult,StructuralProgram.left_denote,StructuralProgram.right_denote]
  exact Laws.assoc _ _ _

end DosenPetric.Reduced.Gentzen.SequentialAdapters
