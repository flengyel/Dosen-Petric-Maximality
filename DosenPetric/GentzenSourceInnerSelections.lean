module

public import DosenPetric.GentzenSourceLogicalCasts

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionSelection
variable {C : NormalForm P} {F K : List (NormalForm P)}

theorem block_cast {U L : List (NormalForm P)} (p : ContractionSelection C F K) (hF : F=U) (hK : K=L) :
    (p.cast hF hK).block=p.block.cast hF hK := by
  cases hF;cases hK;rfl

theorem block_injective (p q : ContractionSelection C F K) (h : p.block=q.block) : p=q := by
  apply eq_of_gs
  exact congrArg ContractionBlock.gs h

theorem cast_perform_rankL {U L Δ : List (NormalForm P)} (p : ContractionSelection C F K)
    (hF : F=U) (hK : K=L) (f : G P U Δ) :
    ((p.cast hF hK).performL Δ f).rho .left (p.cast hF hK).keep=
      (p.performL Δ (f.reindex hF.symm rfl)).rho .left p.keep := by
  cases hF;cases hK;rfl

theorem cast_perform_rankR {U L Δ : List (NormalForm P)} (p : ContractionSelection C F K)
    (hF : F=U) (hK : K=L) (f : G P Δ U) :
    ((p.cast hF hK).performR Δ f).rho .right (p.cast hF hK).keep=
      (p.performR Δ (f.reindex rfl hF.symm)).rho .right p.keep := by
  cases hF;cases hK;rfl

theorem logicalData_innerLower (o : Op) (A B : NormalForm P)
    (p : ContractionSelection (o.formula A B) F K) :
    (p.logicalData o A B).I=K++[A,B] := congrArg (fun F=>F++[A,B]) p.lower

theorem logicalData_inner (o : Op) (A B : NormalForm P)
    (p : ContractionSelection (o.formula A B) F K) :
    ((p.logicalData o A B).inner.cast (p.logicalData_input o A B)
      (p.logicalData_innerLower o A B))=(p.extend [A,B]).block := by
  apply ContractionBlock.ext_data
  · rfl
  · exact (p.extend_gs [A,B]).symm
  · exact (p.extend_tail [A,B]).symm

theorem logicalData_nonempty (o : Op) (A B : NormalForm P)
    (p : ContractionSelection (o.formula A B) F K) : 1≤(p.logicalData o A B).gs.length := by
  change 1≤p.gs.length
  rw [p.count]
  exact p.arity_pos

theorem logicalData_selectionL (A B : NormalForm P) (p : ContractionSelection (.conj A B) F K) :
    ((W4.NonemptyLeft.selection (p.logicalData .conj A B) (p.logicalData_nonempty .conj A B)).cast
      (p.logicalData_input .conj A B) (p.logicalData_innerLower .conj A B))=p.extend [A,B] := by
  apply block_injective
  exact (block_cast _ (p.logicalData_input .conj A B) (p.logicalData_innerLower .conj A B)).trans
    ((congrArg (fun d=>d.cast (p.logicalData_input .conj A B) (p.logicalData_innerLower .conj A B))
      (W4.NonemptyLeft.selection_block _ _)).trans (p.logicalData_inner .conj A B))

theorem logicalData_selectionR (A B : NormalForm P) (p : ContractionSelection (.disj A B) F K) :
    ((W4.NonemptyRight.selection (p.logicalData .disj A B) (p.logicalData_nonempty .disj A B)).cast
      (p.logicalData_input .disj A B) (p.logicalData_innerLower .disj A B))=p.extend [A,B] := by
  apply block_injective
  exact (block_cast _ (p.logicalData_input .disj A B) (p.logicalData_innerLower .disj A B)).trans
    ((congrArg (fun d=>d.cast (p.logicalData_input .disj A B) (p.logicalData_innerLower .disj A B))
      (W4.NonemptyRight.selection_block _ _)).trans (p.logicalData_inner .disj A B))
end ContractionSelection
end DosenPetric.Reduced.Gentzen
