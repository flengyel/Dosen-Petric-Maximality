module

public import DosenPetric.GentzenSelectedLogicalComponents
public import DosenPetric.GentzenAnalysisMacros

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W4.SelectedLogical
universe u
variable {P : Type u}

section L
variable (d : Gentzen.SelectedLogical.Data P .conj) (hn : 2 ≤ d.gs.length)
variable (Δ : List (NormalForm P)) (f : G P d.F Δ)
def logicalL : G P d.U Δ := G.conjL d.s.F [] Δ d.A d.B f
def innerL : G P d.I Δ := d.inner.applyL hn Δ f
def middleL : G P d.J Δ := G.conjL d.s.I [] Δ d.A d.B (innerL d hn Δ f)
def oldL : G P d.K Δ := d.outer.applyL (d.s.outer_bound hn) Δ (logicalL d Δ f)
def newL : G P d.K Δ := d.last.applyL (Nat.le_refl 2) Δ (middleL d hn Δ f)

theorem old_denoteL : ofTerm (oldL d hn Δ f).denote =
    comp (ofTerm d.outer.route.product) (comp (ofTerm (Rules.conjLeft d.s.F [] d.A d.B).toTerm) (ofTerm f.denote)) := d.outer.denoteL ..
theorem new_denoteL : ofTerm (newL d hn Δ f).denote =
    comp (ofTerm d.last.route.product) (comp (ofTerm (Rules.conjLeft d.s.I [] d.A d.B).toTerm) (comp (ofTerm d.inner.route.product) (ofTerm f.denote))) := by
  have h := d.last.denoteL (Nat.le_refl 2) Δ (middleL d hn Δ f)
  change ofTerm (newL d hn Δ f).denote =
    comp (ofTerm d.last.route.product) (comp (ofTerm (Rules.conjLeft d.s.I [] d.A d.B).toTerm) (ofTerm (innerL d hn Δ f).denote)) at h
  exact h.trans (congrArg (fun k => comp (ofTerm d.last.route.product) (comp (ofTerm (Rules.conjLeft d.s.I [] d.A d.B).toTerm) (k))) (d.inner.denoteL hn Δ f))
theorem denoteL : ofTerm (newL d hn Δ f).denote = ofTerm (oldL d hn Δ f).denote := by
  rw [new_denoteL,old_denoteL,← Laws.assoc,← Laws.assoc,← Laws.assoc,d.product_square]

theorem old_countL : (oldL d hn Δ f).cutCount = f.cutCount := by
  simp only [oldL,ContractionBlock.countL,logicalL,G.cutCount]
theorem new_countL : (newL d hn Δ f).cutCount = f.cutCount := by
  simp only [newL,middleL,innerL,ContractionBlock.applyL,G.count_reindex,G.cutCount]
theorem old_cutFreeL : (oldL d hn Δ f).CutFree ↔ f.CutFree := by
  simp only [G.CutFree,old_countL]
theorem new_cutFreeL : (newL d hn Δ f).CutFree ↔ f.CutFree := by
  simp only [G.CutFree,new_countL]
theorem old_atomizedL : (oldL d hn Δ f).Atomized ↔ f.Atomized := by
  simp only [oldL,ContractionBlock.atomizedL,logicalL,G.Atomized]
theorem new_atomizedL : (newL d hn Δ f).Atomized ↔ f.Atomized := by
  simp only [newL,middleL,innerL,ContractionBlock.applyL,G.atomized_reindex,G.Atomized]
theorem relationL : (newL d hn Δ f).relation = (oldL d hn Δ f).relation :=
  congrArg occurrenceMap (denoteL d hn Δ f)
end L

section R
variable (d : Gentzen.SelectedLogical.Data P .disj) (hn : 2 ≤ d.gs.length)
variable (Γ : List (NormalForm P)) (f : G P Γ d.F)
def logicalR : G P Γ d.U := G.disjR Γ d.s.F [] d.A d.B f
def innerR : G P Γ d.I := d.inner.applyR hn Γ f
def middleR : G P Γ d.J := G.disjR Γ d.s.I [] d.A d.B (innerR d hn Γ f)
def oldR : G P Γ d.K := d.outer.applyR (d.s.outer_bound hn) Γ (logicalR d Γ f)
def newR : G P Γ d.K := d.last.applyR (Nat.le_refl 2) Γ (middleR d hn Γ f)

theorem old_denoteR : ofTerm (oldR d hn Γ f).denote =
    comp (comp (ofTerm f.denote) (ofTerm (Rules.disjRight d.s.F [] d.A d.B).toTerm)) (ofTerm d.outer.route.coproduct) := d.outer.denoteR ..
theorem new_denoteR : ofTerm (newR d hn Γ f).denote =
    comp (comp (comp (ofTerm f.denote) (ofTerm d.inner.route.coproduct)) (ofTerm (Rules.disjRight d.s.I [] d.A d.B).toTerm)) (ofTerm d.last.route.coproduct) := by
  have h := d.last.denoteR (Nat.le_refl 2) Γ (middleR d hn Γ f)
  change ofTerm (newR d hn Γ f).denote =
    comp (comp (ofTerm (innerR d hn Γ f).denote) (ofTerm (Rules.disjRight d.s.I [] d.A d.B).toTerm)) (ofTerm d.last.route.coproduct) at h
  exact h.trans (congrArg (fun k => comp (comp (k) (ofTerm (Rules.disjRight d.s.I [] d.A d.B).toTerm)) (ofTerm d.last.route.coproduct)) (d.inner.denoteR hn Γ f))
theorem denoteR : ofTerm (newR d hn Γ f).denote = ofTerm (oldR d hn Γ f).denote := by
  rw [new_denoteR,old_denoteR,Laws.assoc,Laws.assoc,Laws.assoc,d.coproduct_square]

theorem old_countR : (oldR d hn Γ f).cutCount = f.cutCount := by
  simp only [oldR,ContractionBlock.countR,logicalR,G.cutCount]
theorem new_countR : (newR d hn Γ f).cutCount = f.cutCount := by
  simp only [newR,middleR,innerR,ContractionBlock.applyR,G.count_reindex,G.cutCount]
theorem old_cutFreeR : (oldR d hn Γ f).CutFree ↔ f.CutFree := by
  simp only [G.CutFree,old_countR]
theorem new_cutFreeR : (newR d hn Γ f).CutFree ↔ f.CutFree := by
  simp only [G.CutFree,new_countR]
theorem old_atomizedR : (oldR d hn Γ f).Atomized ↔ f.Atomized := by
  simp only [oldR,ContractionBlock.atomizedR,logicalR,G.Atomized]
theorem new_atomizedR : (newR d hn Γ f).Atomized ↔ f.Atomized := by
  simp only [newR,middleR,innerR,ContractionBlock.applyR,G.atomized_reindex,G.Atomized]
theorem relationR : (newR d hn Γ f).relation = (oldR d hn Γ f).relation :=
  congrArg occurrenceMap (denoteR d hn Γ f)
end R

theorem terminal_left (A B : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Δ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (f : G P ((repeated (.conj A B) gs++Θ)++[A,B]) Δ) :
    ofTerm (newL ⟨A,B,gs,Θ⟩ hn Δ f).denote = ofTerm (oldL ⟨A,B,gs,Θ⟩ hn Δ f).denote := denoteL ..
theorem terminal_right (A B : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Γ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (f : G P Γ ((repeated (.disj A B) gs++Θ)++[A,B])) :
    ofTerm (newR ⟨A,B,gs,Θ⟩ hn Γ f).denote = ofTerm (oldR ⟨A,B,gs,Θ⟩ hn Γ f).denote := denoteR ..

end DosenPetric.Reduced.Gentzen.W4.SelectedLogical
