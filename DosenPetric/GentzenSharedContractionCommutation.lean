module

public import DosenPetric.GentzenSharedContractionData

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace SharedContraction.Data
variable (d : Data P) (hn : 2 ≤ d.gs.length) (hm : 2 ≤ d.hs.length) (h : d.Shared)

theorem product_square :
    comp (ofTerm d.outer.route.product) (ofTerm d.inner.route.product) =
      ofTerm (d.flat hn hm h).route.product := by
  apply product_positions
  intro A a
  rw [Laws.assoc,Route.product_get,Route.product_get,Route.product_get]
  exact congrArg (fun x => ofTerm x.projection) (d.square hn hm h a).symm

theorem coproduct_square :
    comp (ofTerm d.inner.route.coproduct) (ofTerm d.outer.route.coproduct) =
      ofTerm (d.flat hn hm h).route.coproduct := by
  apply coproduct_positions
  intro A a
  rw [← Laws.assoc,Route.coproduct_get,Route.coproduct_get,Route.coproduct_get]
  exact congrArg (fun x => ofTerm x.injection) (d.square hn hm h a).symm

theorem weights (r : At d.F d.C → Nat) :
    (d.outer.selected.map (fun b => (((TraceRoute.full d.inner.route).fiber b).map r).sum)).sum =
      ((d.flat hn hm h).selected.map r).sum := by
  have he := TraceRoute.sum_fiber_comp d.inner.route d.outer.route d.outer.keep r
  rw [d.composite hn hm h,d.outer.selected_fiber,← d.keep hn hm h,
    (d.flat hn hm h).selected_fiber] at he
  exact he.symm
end SharedContraction.Data

namespace W3.SharedContraction
variable (d : Gentzen.SharedContraction.Data P) (hn : 2 ≤ d.gs.length)
  (hm : 2 ≤ d.hs.length) (h : d.Shared)

section L
variable (Δ : List (NormalForm P)) (f : G P d.F Δ)
def innerL : G P d.I Δ := d.inner.applyL hn Δ f
def oldL : G P d.K Δ := d.outer.applyL hm Δ (innerL d hn Δ f)
def flatL : G P d.K Δ := (d.flat hn hm h).applyL (d.flat_bound hn hm h) Δ f

theorem denoteL : ofTerm (flatL d hn hm h Δ f).denote = ofTerm (oldL d hn hm Δ f).denote := by
  simp only [flatL,oldL,innerL,ContractionBlock.denoteL]
  rw [← Laws.assoc,d.product_square hn hm h]

theorem old_countL : (oldL d hn hm Δ f).cutCount = f.cutCount := by
  simp only [oldL,innerL,ContractionBlock.countL]
theorem flat_countL : (flatL d hn hm h Δ f).cutCount = f.cutCount :=
  (d.flat hn hm h).countL (d.flat_bound hn hm h) Δ f
theorem old_cutFreeL : (oldL d hn hm Δ f).CutFree ↔ f.CutFree := by
  simp only [G.CutFree,old_countL]
theorem flat_cutFreeL : (flatL d hn hm h Δ f).CutFree ↔ f.CutFree := by
  simp only [G.CutFree,flat_countL]
theorem old_atomizedL : (oldL d hn hm Δ f).Atomized ↔ f.Atomized := by
  simp only [oldL,innerL,ContractionBlock.atomizedL]
theorem flat_atomizedL : (flatL d hn hm h Δ f).Atomized ↔ f.Atomized :=
  (d.flat hn hm h).atomizedL (d.flat_bound hn hm h) Δ f
theorem relationL : (flatL d hn hm h Δ f).relation = (oldL d hn hm Δ f).relation :=
  congrArg occurrenceMap (denoteL d hn hm h Δ f)
end L

section R
variable (Γ : List (NormalForm P)) (f : G P Γ d.F)
def innerR : G P Γ d.I := d.inner.applyR hn Γ f
def oldR : G P Γ d.K := d.outer.applyR hm Γ (innerR d hn Γ f)
def flatR : G P Γ d.K := (d.flat hn hm h).applyR (d.flat_bound hn hm h) Γ f

theorem denoteR : ofTerm (flatR d hn hm h Γ f).denote = ofTerm (oldR d hn hm Γ f).denote := by
  simp only [flatR,oldR,innerR,ContractionBlock.denoteR]
  rw [Laws.assoc,d.coproduct_square hn hm h]

theorem old_countR : (oldR d hn hm Γ f).cutCount = f.cutCount := by
  simp only [oldR,innerR,ContractionBlock.countR]
theorem flat_countR : (flatR d hn hm h Γ f).cutCount = f.cutCount :=
  (d.flat hn hm h).countR (d.flat_bound hn hm h) Γ f
theorem old_cutFreeR : (oldR d hn hm Γ f).CutFree ↔ f.CutFree := by
  simp only [G.CutFree,old_countR]
theorem flat_cutFreeR : (flatR d hn hm h Γ f).CutFree ↔ f.CutFree := by
  simp only [G.CutFree,flat_countR]
theorem old_atomizedR : (oldR d hn hm Γ f).Atomized ↔ f.Atomized := by
  simp only [oldR,innerR,ContractionBlock.atomizedR]
theorem flat_atomizedR : (flatR d hn hm h Γ f).Atomized ↔ f.Atomized :=
  (d.flat hn hm h).atomizedR (d.flat_bound hn hm h) Γ f
theorem relationR : (flatR d hn hm h Γ f).relation = (oldR d hn hm Γ f).relation :=
  congrArg occurrenceMap (denoteR d hn hm h Γ f)
end R
end W3.SharedContraction
end DosenPetric.Reduced.Gentzen
