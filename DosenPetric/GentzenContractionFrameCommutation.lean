module

public import DosenPetric.GentzenContractionFrameFibers

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W1.ContractionFrame
universe u
variable {P : Type u} (d : ContractionFrame P)
variable (hSq : ∀ {A : NormalForm P} (a : At d.F A), d.c1.get (d.e0.get a) = d.e1.get (d.c0.get a))
variable (hn : 2 ≤ d.cgs0.length) (hm : 2 ≤ d.egs0.length)

theorem outerArity (hn : 2 ≤ d.cgs0.length) : 2 ≤ d.bc1.gs.length := d.countC.symm ▸ hn

theorem innerArity (hm : 2 ≤ d.egs0.length) : 2 ≤ d.be1.gs.length := d.countE.symm ▸ hm

section L
variable (Δ : List (NormalForm P)) (f : G P d.F Δ)

def innerCL : G P d.FC Δ := d.bc0.applyL hn Δ f
def innerEL : G P d.FE Δ := d.be0.applyL hm Δ f
def oldL : G P d.K Δ := d.bc1.applyL (outerArity d hn) Δ (innerEL d hm Δ f)
def newL : G P d.K Δ := d.be1.applyL (innerArity d hm) Δ (innerCL d hn Δ f)

include hSq in
theorem denoteL : ofTerm (newL d hn hm Δ f).denote = ofTerm (oldL d hn hm Δ f).denote := by
  simp only [newL,oldL,innerCL,innerEL,ContractionBlock.denoteL]
  rw [← Laws.assoc,← Laws.assoc,d.product_square hSq]

theorem oldL_count : (oldL d hn hm Δ f).cutCount = f.cutCount := by
  simp only [oldL,innerEL,ContractionBlock.countL]

theorem oldL_cutFree : (oldL d hn hm Δ f).CutFree ↔ f.CutFree := by
  simp only [G.CutFree,oldL_count]

theorem oldL_atomized : (oldL d hn hm Δ f).Atomized ↔ f.Atomized := by
  simp only [oldL,innerEL,ContractionBlock.atomizedL]

theorem newL_count : (newL d hn hm Δ f).cutCount = f.cutCount := by
  simp only [newL,innerCL,ContractionBlock.countL]

theorem newL_cutFree : (newL d hn hm Δ f).CutFree ↔ f.CutFree := by
  simp only [G.CutFree,newL_count]

theorem newL_atomized : (newL d hn hm Δ f).Atomized ↔ f.Atomized := by
  simp only [newL,innerCL,ContractionBlock.atomizedL]

theorem cutCountL : (newL d hn hm Δ f).cutCount = (oldL d hn hm Δ f).cutCount :=
  (newL_count ..).trans (oldL_count ..).symm

theorem cutFreeL : (newL d hn hm Δ f).CutFree ↔ (oldL d hn hm Δ f).CutFree :=
  (newL_cutFree ..).trans (oldL_cutFree ..).symm

theorem atomizedL : (newL d hn hm Δ f).Atomized ↔ (oldL d hn hm Δ f).Atomized :=
  (newL_atomized ..).trans (oldL_atomized ..).symm

include hSq in
theorem relationL : (newL d hn hm Δ f).relation = (oldL d hn hm Δ f).relation :=
  congrArg occurrenceMap (denoteL d hSq hn hm Δ f)

end L
section R
variable (Γ : List (NormalForm P)) (f : G P Γ d.F)

def innerCR : G P Γ d.FC := d.bc0.applyR hn Γ f
def innerER : G P Γ d.FE := d.be0.applyR hm Γ f
def oldR : G P Γ d.K := d.bc1.applyR (outerArity d hn) Γ (innerER d hm Γ f)
def newR : G P Γ d.K := d.be1.applyR (innerArity d hm) Γ (innerCR d hn Γ f)

include hSq in
theorem denoteR : ofTerm (newR d hn hm Γ f).denote = ofTerm (oldR d hn hm Γ f).denote := by
  simp only [newR,oldR,innerCR,innerER,ContractionBlock.denoteR]
  rw [Laws.assoc,Laws.assoc,d.coproduct_square hSq]

theorem oldR_count : (oldR d hn hm Γ f).cutCount = f.cutCount := by
  simp only [oldR,innerER,ContractionBlock.countR]

theorem oldR_cutFree : (oldR d hn hm Γ f).CutFree ↔ f.CutFree := by
  simp only [G.CutFree,oldR_count]

theorem oldR_atomized : (oldR d hn hm Γ f).Atomized ↔ f.Atomized := by
  simp only [oldR,innerER,ContractionBlock.atomizedR]

theorem newR_count : (newR d hn hm Γ f).cutCount = f.cutCount := by
  simp only [newR,innerCR,ContractionBlock.countR]

theorem newR_cutFree : (newR d hn hm Γ f).CutFree ↔ f.CutFree := by
  simp only [G.CutFree,newR_count]

theorem newR_atomized : (newR d hn hm Γ f).Atomized ↔ f.Atomized := by
  simp only [newR,innerCR,ContractionBlock.atomizedR]

theorem cutCountR : (newR d hn hm Γ f).cutCount = (oldR d hn hm Γ f).cutCount :=
  (newR_count ..).trans (oldR_count ..).symm

theorem cutFreeR : (newR d hn hm Γ f).CutFree ↔ (oldR d hn hm Γ f).CutFree :=
  (newR_cutFree ..).trans (oldR_cutFree ..).symm

theorem atomizedR : (newR d hn hm Γ f).Atomized ↔ (oldR d hn hm Γ f).Atomized :=
  (newR_atomized ..).trans (oldR_atomized ..).symm

include hSq in
theorem relationR : (newR d hn hm Γ f).relation = (oldR d hn hm Γ f).relation :=
  congrArg occurrenceMap (denoteR d hSq hn hm Γ f)

end R
end DosenPetric.Reduced.Gentzen.W1.ContractionFrame
