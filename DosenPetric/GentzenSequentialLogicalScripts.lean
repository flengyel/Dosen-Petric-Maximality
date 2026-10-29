module

public import DosenPetric.GentzenTerminalLogicalHeadSquare

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialLogical
universe u
variable {P : Type u}

def components {F : List (NormalForm P)} {C : NormalForm P} (a : At F C)
    (A B : NormalForm P) : ExchangeScript P (C::A::B::a.erase) (F++[A,B]) :=
  ((BinaryMix.swapWhole a.erase [A,B]).consFixed C).seq (LogicalDeletion.headBefore a [A,B])

def principal {F : List (NormalForm P)} {C : NormalForm P} (a : At F C)
    (Q : NormalForm P) : ExchangeScript P (C::Q::a.erase) (F++[Q]) :=
  ((BinaryMix.swapWhole a.erase [Q]).consFixed C).seq (LogicalDeletion.headBefore a [Q])

theorem components_selected {F : List (NormalForm P)} {C : NormalForm P} (a : At F C)
    (A B : NormalForm P) :
    (components a A B).get (a.before [A,B]) = .here C (A::B::a.erase) := by
  change ((BinaryMix.swapWhole a.erase [A,B]).consFixed C).get
    ((LogicalDeletion.headBefore a [A,B]).get (a.before [A,B])) = _
  rw [LogicalDeletion.headBefore_selected,ExchangeScript.consFixed_here]
  rfl

theorem principal_square (o : Op) {F : List (NormalForm P)} {C : NormalForm P}
    (a : At F C) (A B : NormalForm P) :
    (side P o).comp ((principal a (o.formula A B)).arrow o) (logicalSide o F [] A B) =
      (side P o).comp (logicalSide o [C] a.erase A B) ((components a A B).arrow o) := by
  let S := side P o
  let M := sideM P o
  rw [principal,components,ExchangeScript.seq_side_arrow,ExchangeScript.seq_side_arrow,
    ExchangeScript.consFixed_arrow,ExchangeScript.consFixed_arrow,S.assoc,
    LogicalDeletion.before_square,← S.assoc,M.tensor_comp,S.id_comp,
    terminal_logical_head_square,logicalSide_cons,← S.assoc,M.tensor_comp,S.id_comp]
  rfl

end DosenPetric.Reduced.Gentzen.SequentialLogical
