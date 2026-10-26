module

public import DosenPetric.GentzenNonemptyLeftBounds
public import DosenPetric.GentzenNonemptyRightBounds
public import DosenPetric.GentzenTerminalSelectionFactor

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionBlock

def cast {F K U L : List (NormalForm P)} (hF : F=U) (hK : K=L)
    (d : ContractionBlock P F K) : ContractionBlock P U L :=
  ⟨d.C,d.gs,d.tail,d.upper.trans hF,d.lower.trans hK⟩
end ContractionBlock
namespace ContractionSelection
variable {C : NormalForm P} {F K : List (NormalForm P)}

theorem terminal_gs (p : ContractionSelection C F K) :
    (p.chain (.last [])).gs=p.gs++[p.tail] := by
  rw [p.chain_gs]
  simp only [first,rest,List.append_nil]

theorem terminal_tail (p : ContractionSelection C F K) : (p.chain (.last [])).tail=[] :=
  p.chain_tail (.last [])

/-- Published terminal unary-logical data determined by an existing positional
selection. Its endpoint equations remain explicit. -/
def logicalData (o : Op) (A B : NormalForm P)
    (p : ContractionSelection (o.formula A B) F K) : SelectedLogical.Data P o :=
  ⟨A,B,p.gs,p.tail⟩

theorem logicalData_source (o : Op) (A B : NormalForm P)
    (p : ContractionSelection (o.formula A B) F K) :
    (p.logicalData o A B).s.F=F := p.upper

theorem logicalData_input (o : Op) (A B : NormalForm P)
    (p : ContractionSelection (o.formula A B) F K) :
    (p.logicalData o A B).F=F++[A,B] := congrArg (fun F=>F++[A,B]) p.upper

theorem logicalData_upper (o : Op) (A B : NormalForm P)
    (p : ContractionSelection (o.formula A B) F K) :
    (p.logicalData o A B).U=F++[o.formula A B] := congrArg (fun F=>F++[o.formula A B]) p.upper

theorem logicalData_lower (o : Op) (A B : NormalForm P)
    (p : ContractionSelection (o.formula A B) F K) :
    (p.logicalData o A B).K=p.erased++[o.formula A B] :=
  congrArg (fun F=>F++[o.formula A B]) p.erased_eq.symm

theorem logicalData_outer (o : Op) (A B : NormalForm P)
    (p : ContractionSelection (o.formula A B) F K) :
    ((p.logicalData o A B).outer.cast (p.logicalData_upper o A B) (p.logicalData_lower o A B))=
      (p.chain (.last [])).block := by
  apply ContractionBlock.ext_data
  · rfl
  · exact p.terminal_gs.symm
  · exact p.terminal_tail.symm
end ContractionSelection
end DosenPetric.Reduced.Gentzen
