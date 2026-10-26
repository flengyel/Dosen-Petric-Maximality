module

public import DosenPetric.GentzenSourceInnerSelections

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.SelectedLogicalReducer
universe u
variable {P : Type u} {A B : NormalForm P} {F L Δ : List (NormalForm P)}

section Left
variable (p : ContractionSelection (.conj A B) F L) (f : G P (F++[A,B]) Δ)

def sourceRepairL : G P (p.erased++[.conj A B]) Δ :=
  W4.NonemptyLeft.transported (p.logicalData .conj A B) (p.logicalData_nonempty .conj A B)
    (p.logicalData_source .conj A B) (p.logicalData_lower .conj A B) Δ f

def sourceInnerL : Nat := W4.NonemptyLeft.innerRank (p.logicalData .conj A B)
  (p.logicalData_nonempty .conj A B) Δ (f.reindex (p.logicalData_input .conj A B).symm rfl)

theorem terminal_arityL : 2≤(terminal p).arity := by
  rw [terminal,p.chain_count]
  change 2≤p.arity+1
  have hp:=p.arity_pos
  omega

theorem sourceDenoteL : ofTerm (sourceRepairL p f).denote=
    ofTerm ((terminal p).performL Δ (G.conjL F [] Δ A B f)).denote := by
  have h:=W4.NonemptyLeft.transported_denote (p.logicalData .conj A B)
    (p.logicalData_nonempty .conj A B) (p.logicalData_source .conj A B) (p.logicalData_lower .conj A B) Δ f
  refine h.trans ?_
  exact congrArg (fun g : G P (p.erased++[.conj A B]) Δ=>ofTerm g.denote)
    ((ContractionBlock.applyL_congr (p.logicalData_outer .conj A B) _ _ _ _).trans
      ((terminal p).performL_eq_apply (terminal_arityL p) _).symm)

theorem sourceCountL : (sourceRepairL p f).cutCount=f.cutCount :=
  W4.NonemptyLeft.transported_count ..

theorem sourceBoundL : ContractionBound .left (.conj A B) (sourceInnerL p f+1) (sourceRepairL p f)
    (fun a=>a.index=(p.logicalData .conj A B).x.index) :=
  W4.NonemptyLeft.transported_bound (p.logicalData .conj A B) (p.logicalData_nonempty .conj A B)
    (p.logicalData_source .conj A B) (p.logicalData_lower .conj A B) Δ f

theorem sourceInnerL_eq : sourceInnerL p f=
    ((p.extend [A,B]).performL Δ f).rho .left (p.extend [A,B]).keep := by
  let d:=p.logicalData .conj A B
  let hn:=p.logicalData_nonempty .conj A B
  let s:=W4.NonemptyLeft.selection d hn
  have he:=p.logicalData_selectionL A B
  have hcast:=s.cast_perform_rankL (p.logicalData_input .conj A B)
    (p.logicalData_innerLower .conj A B) f
  have hh:=congrArg
    (fun q : ContractionSelection (.conj A B) (F++[A,B]) (L++[A,B])=>
      (q.performL Δ f).rho .left q.keep) he
  have hk:=congrArg
    (fun x : At d.I d.C=>(s.performL Δ (f.reindex (p.logicalData_input .conj A B).symm rfl)).rho .left x)
    (W4.NonemptyLeft.selection_keep d hn)
  exact hk.symm.trans (hcast.symm.trans hh)
end Left

section Right
variable (p : ContractionSelection (.disj A B) F L) (f : G P Δ (F++[A,B]))

def sourceRepairR : G P Δ (p.erased++[.disj A B]) :=
  W4.NonemptyRight.transported (p.logicalData .disj A B) (p.logicalData_nonempty .disj A B)
    (p.logicalData_source .disj A B) (p.logicalData_lower .disj A B) Δ f

def sourceInnerR : Nat := W4.NonemptyRight.innerRank (p.logicalData .disj A B)
  (p.logicalData_nonempty .disj A B) Δ (f.reindex rfl (p.logicalData_input .disj A B).symm)

theorem terminal_arityR : 2≤(terminal p).arity := by
  rw [terminal,p.chain_count]
  change 2≤p.arity+1
  have hp:=p.arity_pos
  omega

theorem sourceDenoteR : ofTerm (sourceRepairR p f).denote=
    ofTerm ((terminal p).performR Δ (G.disjR Δ F [] A B f)).denote := by
  have h:=W4.NonemptyRight.transported_denote (p.logicalData .disj A B)
    (p.logicalData_nonempty .disj A B) (p.logicalData_source .disj A B) (p.logicalData_lower .disj A B) Δ f
  refine h.trans ?_
  exact congrArg (fun g : G P Δ (p.erased++[.disj A B])=>ofTerm g.denote)
    ((ContractionBlock.applyR_congr (p.logicalData_outer .disj A B) _ _ _ _).trans
      ((terminal p).performR_eq_apply (terminal_arityR p) _).symm)

theorem sourceCountR : (sourceRepairR p f).cutCount=f.cutCount :=
  W4.NonemptyRight.transported_count ..

theorem sourceBoundR : ContractionBound .right (.disj A B) (sourceInnerR p f+1) (sourceRepairR p f)
    (fun a=>a.index=(p.logicalData .disj A B).x.index) :=
  W4.NonemptyRight.transported_bound (p.logicalData .disj A B) (p.logicalData_nonempty .disj A B)
    (p.logicalData_source .disj A B) (p.logicalData_lower .disj A B) Δ f

theorem sourceInnerR_eq : sourceInnerR p f=
    ((p.extend [A,B]).performR Δ f).rho .right (p.extend [A,B]).keep := by
  let d:=p.logicalData .disj A B
  let hn:=p.logicalData_nonempty .disj A B
  let s:=W4.NonemptyRight.selection d hn
  have he:=p.logicalData_selectionR A B
  have hcast:=s.cast_perform_rankR (p.logicalData_input .disj A B)
    (p.logicalData_innerLower .disj A B) f
  have hh:=congrArg
    (fun q : ContractionSelection (.disj A B) (F++[A,B]) (L++[A,B])=>
      (q.performR Δ f).rho .right q.keep) he
  have hk:=congrArg
    (fun x : At d.I d.C=>(s.performR Δ (f.reindex rfl (p.logicalData_input .disj A B).symm)).rho .right x)
    (W4.NonemptyRight.selection_keep d hn)
  exact hk.symm.trans (hcast.symm.trans hh)
end Right
end DosenPetric.Reduced.Gentzen.SelectedLogicalReducer
