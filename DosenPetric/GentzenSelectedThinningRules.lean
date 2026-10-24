module

public import DosenPetric.GentzenSelectedThinningFibers
public import DosenPetric.GentzenAnalysisMacros

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W2.SelectedThinning
universe u
variable {P : Type u} (d : Gentzen.SelectedThinning.Data P) (hn : 2 ≤ d.gs.length)

section L
variable (Δ : List (NormalForm P)) (f : G P d.F Δ)

def thinL : G P d.U Δ := UnaryCast.thinL d.F [] d.C d.thinSource rfl Δ f
def innerL : G P d.I Δ := d.inner.applyL hn Δ f
def oldL : G P d.K Δ := d.outer.applyL (d.outer_bound hn) Δ (thinL d Δ f)
def newL : G P d.K Δ :=
  UnaryCast.exchangeL (gaps d.gs) [d.C] d.Θ [] d.exchangeSource d.exchangeTarget Δ (innerL d hn Δ f)

theorem thin_denoteL : ofTerm (thinL d Δ f).denote =
    comp (ofTerm d.t.product) (ofTerm f.denote) := UnaryCast.thinL_denote ..
theorem inner_denoteL : ofTerm (innerL d hn Δ f).denote =
    comp (ofTerm d.inner.route.product) (ofTerm f.denote) := d.inner.denoteL hn Δ f
theorem old_denoteL : ofTerm (oldL d hn Δ f).denote =
    comp (ofTerm d.outer.route.product) (comp (ofTerm d.t.product) (ofTerm f.denote)) := by
  exact (d.outer.denoteL (d.outer_bound hn) Δ (thinL d Δ f)).trans
    (congrArg (comp (ofTerm d.outer.route.product)) (thin_denoteL d Δ f))
theorem new_denoteL : ofTerm (newL d hn Δ f).denote =
    comp (ofTerm d.e.product) (ofTerm (innerL d hn Δ f).denote) := UnaryCast.exchangeL_denote ..
theorem denoteL : ofTerm (newL d hn Δ f).denote = ofTerm (oldL d hn Δ f).denote := by
  rw [new_denoteL,inner_denoteL,old_denoteL,← Laws.assoc,← Laws.assoc,d.product_square]

theorem old_countL : (oldL d hn Δ f).cutCount = f.cutCount := by
  simp only [oldL,ContractionBlock.countL,thinL,UnaryCast.thinL,G.count_reindex,G.cutCount]
theorem new_countL : (newL d hn Δ f).cutCount = f.cutCount := by
  simp only [newL,UnaryCast.exchangeL,G.count_reindex,G.cutCount,innerL,ContractionBlock.countL]
theorem old_cutFreeL : (oldL d hn Δ f).CutFree ↔ f.CutFree := by simp only [G.CutFree,old_countL]
theorem new_cutFreeL : (newL d hn Δ f).CutFree ↔ f.CutFree := by simp only [G.CutFree,new_countL]
theorem old_atomizedL : (oldL d hn Δ f).Atomized ↔ AtomicFormula d.C ∧ f.Atomized := by
  simp only [oldL,ContractionBlock.atomizedL,thinL,UnaryCast.thinL,G.atomized_reindex,G.Atomized]
theorem new_atomizedL : (newL d hn Δ f).Atomized ↔ f.Atomized := by
  simp only [newL,UnaryCast.exchangeL,G.atomized_reindex,G.Atomized,innerL,ContractionBlock.atomizedL]
theorem atomized_forwardL (ha : (oldL d hn Δ f).Atomized) : (newL d hn Δ f).Atomized :=
  (new_atomizedL d hn Δ f).mpr ((old_atomizedL d hn Δ f).mp ha).2
theorem atomized_reverseL (hc : AtomicFormula d.C) (ha : (newL d hn Δ f).Atomized) :
    (oldL d hn Δ f).Atomized :=
  (old_atomizedL d hn Δ f).mpr ⟨hc,(new_atomizedL d hn Δ f).mp ha⟩
theorem relationL : (newL d hn Δ f).relation = (oldL d hn Δ f).relation :=
  congrArg occurrenceMap (denoteL d hn Δ f)
end L

section R
variable (Γ : List (NormalForm P)) (f : G P Γ d.F)

def thinR : G P Γ d.U := UnaryCast.thinR d.F [] d.C d.thinSource rfl Γ f
def innerR : G P Γ d.I := d.inner.applyR hn Γ f
def oldR : G P Γ d.K := d.outer.applyR (d.outer_bound hn) Γ (thinR d Γ f)
def newR : G P Γ d.K :=
  UnaryCast.exchangeR (gaps d.gs) [d.C] d.Θ [] d.exchangeSource d.exchangeTarget Γ (innerR d hn Γ f)

theorem thin_denoteR : ofTerm (thinR d Γ f).denote =
    comp (ofTerm f.denote) (ofTerm d.t.coproduct) := UnaryCast.thinR_denote ..
theorem inner_denoteR : ofTerm (innerR d hn Γ f).denote =
    comp (ofTerm f.denote) (ofTerm d.inner.route.coproduct) := d.inner.denoteR hn Γ f
theorem old_denoteR : ofTerm (oldR d hn Γ f).denote =
    comp (comp (ofTerm f.denote) (ofTerm d.t.coproduct)) (ofTerm d.outer.route.coproduct) := by
  exact (d.outer.denoteR (d.outer_bound hn) Γ (thinR d Γ f)).trans
    (congrArg (fun x => comp x (ofTerm d.outer.route.coproduct)) (thin_denoteR d Γ f))
theorem new_denoteR : ofTerm (newR d hn Γ f).denote =
    comp (ofTerm (innerR d hn Γ f).denote) (ofTerm d.e.coproduct) := UnaryCast.exchangeR_denote ..
theorem denoteR : ofTerm (newR d hn Γ f).denote = ofTerm (oldR d hn Γ f).denote := by
  rw [new_denoteR,inner_denoteR,old_denoteR,Laws.assoc,Laws.assoc,d.coproduct_square]

theorem old_countR : (oldR d hn Γ f).cutCount = f.cutCount := by
  simp only [oldR,ContractionBlock.countR,thinR,UnaryCast.thinR,G.count_reindex,G.cutCount]
theorem new_countR : (newR d hn Γ f).cutCount = f.cutCount := by
  simp only [newR,UnaryCast.exchangeR,G.count_reindex,G.cutCount,innerR,ContractionBlock.countR]
theorem old_cutFreeR : (oldR d hn Γ f).CutFree ↔ f.CutFree := by simp only [G.CutFree,old_countR]
theorem new_cutFreeR : (newR d hn Γ f).CutFree ↔ f.CutFree := by simp only [G.CutFree,new_countR]
theorem old_atomizedR : (oldR d hn Γ f).Atomized ↔ AtomicFormula d.C ∧ f.Atomized := by
  simp only [oldR,ContractionBlock.atomizedR,thinR,UnaryCast.thinR,G.atomized_reindex,G.Atomized]
theorem new_atomizedR : (newR d hn Γ f).Atomized ↔ f.Atomized := by
  simp only [newR,UnaryCast.exchangeR,G.atomized_reindex,G.Atomized,innerR,ContractionBlock.atomizedR]
theorem atomized_forwardR (ha : (oldR d hn Γ f).Atomized) : (newR d hn Γ f).Atomized :=
  (new_atomizedR d hn Γ f).mpr ((old_atomizedR d hn Γ f).mp ha).2
theorem atomized_reverseR (hc : AtomicFormula d.C) (ha : (newR d hn Γ f).Atomized) :
    (oldR d hn Γ f).Atomized :=
  (old_atomizedR d hn Γ f).mpr ⟨hc,(new_atomizedR d hn Γ f).mp ha⟩
theorem relationR : (newR d hn Γ f).relation = (oldR d hn Γ f).relation :=
  congrArg occurrenceMap (denoteR d hn Γ f)
end R

theorem terminal_left (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Δ : List (NormalForm P)) (hn : 2 ≤ gs.length) (f : G P (repeated C gs++Θ) Δ) :
    ofTerm (newL ⟨C,gs,Θ⟩ hn Δ f).denote = ofTerm (oldL ⟨C,gs,Θ⟩ hn Δ f).denote := denoteL ..
theorem terminal_right (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Γ : List (NormalForm P)) (hn : 2 ≤ gs.length) (f : G P Γ (repeated C gs++Θ)) :
    ofTerm (newR ⟨C,gs,Θ⟩ hn Γ f).denote = ofTerm (oldR ⟨C,gs,Θ⟩ hn Γ f).denote := denoteR ..

end DosenPetric.Reduced.Gentzen.W2.SelectedThinning
