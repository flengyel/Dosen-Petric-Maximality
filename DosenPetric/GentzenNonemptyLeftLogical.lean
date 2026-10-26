module

public import DosenPetric.GentzenSelectedLogicalRules
public import DosenPetric.GentzenSelectedLogicalRanks
public import DosenPetric.GentzenCenteredBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W4.NonemptyLeft
universe u
variable {P : Type u} (d : Gentzen.SelectedLogical.Data P .conj)
variable (hn : 1≤d.gs.length)
include hn

theorem nonempty : d.gs ≠ [] := by intro he; rw [he] at hn; cases hn
def selection : ContractionSelection d.C d.F d.I := d.inner.selection (nonempty d hn)
theorem selection_block : (selection d hn).block = d.inner := d.inner.selection_block (nonempty d hn)
theorem selection_route : (selection d hn).route = d.inner.route :=
  (selection d hn).route_eq.trans (congrArg ContractionBlock.route (selection_block d hn))
theorem selection_keep : (selection d hn).keep = d.inner.keep := by
  apply At.index_injective
  rw [ContractionSelection.keep_index,ContractionBlock.keep_index]
  exact congrArg (fun b => (gaps b.gs).length) (selection_block d hn)
theorem selection_selected : (selection d hn).selected = d.inner.selected := by
  apply At.list_index_injective
  exact (congrArg (List.map At.index) (selection d hn).selected_eq).trans
    ((selection d hn).block.selected_indices.trans
      ((congrArg (fun b => copyOffsets b.gs) (selection_block d hn)).trans d.inner.selected_indices.symm))
theorem selection_arity : (selection d hn).arity = d.gs.length :=
  (selection d hn).count.symm.trans (congrArg (fun b => b.gs.length) (selection_block d hn))
theorem outerArity : 2 ≤ d.outer.gs.length := by
  change 2 ≤ d.s.outerGaps.length
  rw [d.s.outer_count]
  change 2 ≤ d.gs.length+1
  omega

variable (Δ : List (NormalForm P)) (f : G P d.F Δ)
def inner : G P d.I Δ := (selection d hn).performL Δ f
def old : G P d.K Δ := d.outer.applyL (outerArity d hn) Δ (W4.SelectedLogical.logicalL d Δ f)
def middle : G P d.J Δ := G.conjL d.s.I [] Δ d.A d.B (inner d hn Δ f)
def repair : G P d.K Δ := d.last.applyL (Nat.le_refl 2) Δ (middle d hn Δ f)

theorem inner_denote : ofTerm (inner d hn Δ f).denote=
    comp (ofTerm d.inner.route.product) (ofTerm f.denote) := by
  have h:=(selection d hn).performL_denote Δ f
  rw [selection_route] at h
  exact h

theorem repair_blocked : BlockedL (repair d hn Δ f) := by
  have h:=BlockedL.conjunction d.A d.B (gaps d.gs) d.Θ Δ (inner d hn Δ f)
  simpa only [repair,middle,ContractionBlock.applyL,BlockedSource.left2,
    BlockedSource.conjLLast,G.reindex_trans] using h.reindex d.lastTarget rfl

theorem denote : ofTerm (repair d hn Δ f).denote=ofTerm (old d hn Δ f).denote := by
  have h0:=d.outer.denoteL (outerArity d hn) Δ (W4.SelectedLogical.logicalL d Δ f)
  have h1:=d.last.denoteL (Nat.le_refl 2) Δ (middle d hn Δ f)
  change ofTerm (old d hn Δ f).denote=
    comp (ofTerm d.outer.route.product) (comp (ofTerm (Rules.conjLeft d.s.F [] d.A d.B).toTerm)
      (ofTerm f.denote)) at h0
  change ofTerm (repair d hn Δ f).denote=
    comp (ofTerm d.last.route.product) (comp (ofTerm (Rules.conjLeft d.s.I [] d.A d.B).toTerm)
      (ofTerm (inner d hn Δ f).denote)) at h1
  rw [h0,h1,inner_denote,←Laws.assoc,←Laws.assoc,←Laws.assoc,d.product_square]

theorem count : (repair d hn Δ f).cutCount=f.cutCount := by
  simp only [repair,middle,inner,ContractionBlock.countL,G.cutCount,ContractionSelection.performL_count]

theorem old_count : (old d hn Δ f).cutCount=f.cutCount := by
  simp only [old,ContractionBlock.countL,W4.SelectedLogical.logicalL,G.cutCount]

theorem atomized : (repair d hn Δ f).Atomized↔f.Atomized := by
  simp only [repair,middle,inner,ContractionBlock.atomizedL,G.Atomized,ContractionSelection.performL_atomized]
end DosenPetric.Reduced.Gentzen.W4.NonemptyLeft
