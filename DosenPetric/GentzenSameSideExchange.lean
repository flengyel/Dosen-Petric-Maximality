module

public import DosenPetric.GentzenGapExchangeRouting
public import DosenPetric.GentzenSameSideThinning
public import DosenPetric.GentzenAnalysisMacros

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace W1.SameSideExchange
variable (d : GapExchange.Data P) (hn : 2 ≤ d.gs0.length)

theorem modifiedArity (hn : 2 ≤ d.gs0.length) : 2 ≤ d.gs1.length := d.count_eq.symm ▸ hn

section Left
variable (Δ : List (NormalForm P)) (f : G P d.U0 Δ)

def innerL : G P d.K0 Δ :=
  (G.contractL d.C d.gs0 d.tail0 Δ hn (f.reindex d.upper0.symm rfl)).reindex d.lower0 rfl

def oldL : G P d.K1 Δ :=
  (G.contractL d.C d.gs1 d.tail1 Δ (modifiedArity d hn)
    ((G.exchangeL d.upBefore d.X d.Y d.upAfter Δ f).reindex d.upper1.symm rfl)).reindex d.lower1 rfl

def newL : G P d.K1 Δ := G.exchangeL d.loBefore d.X d.Y d.loAfter Δ (innerL d hn Δ f)

theorem innerL_denote : ofTerm (innerL d hn Δ f).denote = comp (ofTerm d.c0.product) (ofTerm f.denote) :=
  contractL_cast_denote d.C d.gs0 d.tail0 hn d.lower0 d.upper0 f

theorem oldL_denote : ofTerm (oldL d hn Δ f).denote =
    comp (ofTerm d.c1.product) (comp (d.eUpperL) (ofTerm f.denote)) :=
  contractL_cast_denote d.C d.gs1 d.tail1 (modifiedArity d hn) d.lower1 d.upper1 _

theorem denoteL : ofTerm (newL d hn Δ f).denote = ofTerm (oldL d hn Δ f).denote := by
  change comp (d.eLowerL) (ofTerm (innerL d hn Δ f).denote) = _
  rw [innerL_denote,oldL_denote,← Laws.assoc,← Laws.assoc,d.product_square]

theorem cutCountL : (newL d hn Δ f).cutCount = (oldL d hn Δ f).cutCount := by
  simp only [newL,oldL,innerL,G.count_reindex,G.cutCount]

theorem cutFreeL : (newL d hn Δ f).CutFree ↔ (oldL d hn Δ f).CutFree := by
  simp only [G.CutFree,cutCountL]

theorem atomizedL : (newL d hn Δ f).Atomized ↔ (oldL d hn Δ f).Atomized := by
  simp only [newL,oldL,innerL,G.atomized_reindex,G.Atomized]

theorem newL_atomized_iff : (newL d hn Δ f).Atomized ↔ f.Atomized := by
  simp only [newL,innerL,G.atomized_reindex,G.Atomized]

theorem oldL_atomized_iff : (oldL d hn Δ f).Atomized ↔ f.Atomized := by
  simp only [oldL,G.atomized_reindex,G.Atomized]

theorem newL_atomized (hf : f.Atomized) : (newL d hn Δ f).Atomized := by
  simpa only [newL,innerL,G.atomized_reindex,G.Atomized] using hf

theorem relationL : (newL d hn Δ f).relation = (oldL d hn Δ f).relation :=
  congrArg occurrenceMap (denoteL d hn Δ f)

end Left

section Right
variable (Γ : List (NormalForm P)) (f : G P Γ d.U0)

def innerR : G P Γ d.K0 :=
  (G.contractR Γ d.C d.gs0 d.tail0 hn (f.reindex rfl d.upper0.symm)).reindex rfl d.lower0

def oldR : G P Γ d.K1 :=
  (G.contractR Γ d.C d.gs1 d.tail1 (modifiedArity d hn)
    ((G.exchangeR Γ d.upBefore d.X d.Y d.upAfter f).reindex rfl d.upper1.symm)).reindex rfl d.lower1

def newR : G P Γ d.K1 := G.exchangeR Γ d.loBefore d.X d.Y d.loAfter (innerR d hn Γ f)

theorem innerR_denote : ofTerm (innerR d hn Γ f).denote = comp (ofTerm f.denote) (ofTerm d.c0.coproduct) :=
  contractR_cast_denote d.C d.gs0 d.tail0 hn d.lower0 d.upper0 f

theorem oldR_denote : ofTerm (oldR d hn Γ f).denote =
    comp (comp (ofTerm f.denote) (d.eUpperR)) (ofTerm d.c1.coproduct) :=
  contractR_cast_denote d.C d.gs1 d.tail1 (modifiedArity d hn) d.lower1 d.upper1 _

theorem denoteR : ofTerm (newR d hn Γ f).denote = ofTerm (oldR d hn Γ f).denote := by
  change comp (ofTerm (innerR d hn Γ f).denote) (d.eLowerR) = _
  rw [innerR_denote,oldR_denote,Laws.assoc,Laws.assoc,d.coproduct_square]

theorem cutCountR : (newR d hn Γ f).cutCount = (oldR d hn Γ f).cutCount := by
  simp only [newR,oldR,innerR,G.count_reindex,G.cutCount]

theorem cutFreeR : (newR d hn Γ f).CutFree ↔ (oldR d hn Γ f).CutFree := by
  simp only [G.CutFree,cutCountR]

theorem atomizedR : (newR d hn Γ f).Atomized ↔ (oldR d hn Γ f).Atomized := by
  simp only [newR,oldR,innerR,G.atomized_reindex,G.Atomized]

theorem newR_atomized_iff : (newR d hn Γ f).Atomized ↔ f.Atomized := by
  simp only [newR,innerR,G.atomized_reindex,G.Atomized]

theorem oldR_atomized_iff : (oldR d hn Γ f).Atomized ↔ f.Atomized := by
  simp only [oldR,G.atomized_reindex,G.Atomized]

theorem newR_atomized (hf : f.Atomized) : (newR d hn Γ f).Atomized := by
  simpa only [newR,innerR,G.atomized_reindex,G.Atomized] using hf

theorem relationR : (newR d hn Γ f).relation = (oldR d hn Γ f).relation :=
  congrArg occurrenceMap (denoteR d hn Γ f)

end Right
end W1.SameSideExchange
end DosenPetric.Reduced.Gentzen
