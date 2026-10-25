module

public import DosenPetric.GentzenRightLogicalRepairComponents
public import DosenPetric.GentzenSelectionRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W4.NonemptyRight
universe u
variable {P : Type u} (d : Gentzen.SelectedLogical.Data P .disj)
variable (hn : 1 ≤ d.gs.length)
include hn
open HeadRight (block moveRoute moveSource moveTarget blockTarget)

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

variable (Γ : List (NormalForm P)) (f : G P Γ d.F)
def inner : G P Γ d.I := (selection d hn).performR Γ f
def old : G P Γ d.K := d.outer.applyR (outerArity d hn) Γ (W4.SelectedLogical.logicalR d Γ f)
def moved : G P Γ (d.A::d.B::d.s.I) :=
  UnaryCast.exchangeR [] d.s.I [d.A,d.B] [] (moveSource d) (moveTarget d) Γ (inner d hn Γ f)
def head : G P Γ (d.C::d.s.I) := G.disjR Γ [] d.s.I d.A d.B (moved d hn Γ f)
def middle : G P Γ d.s.I := (block d).applyR (Nat.le_refl 2) Γ (head d hn Γ f)
def repair : G P Γ d.K := UnaryCast.exchangeR (gaps d.gs) [d.C] d.Θ []
  d.s.exchangeSource d.s.exchangeTarget Γ (middle d hn Γ f)

theorem inner_denote : ofTerm (inner d hn Γ f).denote =
    comp (ofTerm f.denote) (ofTerm d.inner.route.coproduct) := by
  have h := (selection d hn).performR_denote Γ f
  rw [selection_route] at h
  exact h

theorem middle_blocked : BlockedR (middle d hn Γ f) := by
  have h := BlockedR.disjunction d.A d.B Γ (gaps d.gs) d.Θ (moved d hn Γ f)
  simpa only [middle,head,ContractionBlock.applyR,BlockedSource.right2,G.reindex_trans]
    using h.reindex rfl (blockTarget d)

theorem denote : ofTerm (repair d hn Γ f).denote = ofTerm (old d hn Γ f).denote := by
  have ho := UnaryCast.exchangeR_denote (gaps d.gs) [d.C] d.Θ []
    d.s.exchangeSource d.s.exchangeTarget Γ (middle d hn Γ f)
  change ofTerm (repair d hn Γ f).denote =
    comp (ofTerm (middle d hn Γ f).denote) (ofTerm d.s.e.coproduct) at ho
  have hb := (block d).denoteR (Nat.le_refl 2) Γ (head d hn Γ f)
  change ofTerm (middle d hn Γ f).denote =
    comp (ofTerm (head d hn Γ f).denote) (ofTerm (block d).route.coproduct) at hb
  have hm := UnaryCast.exchangeR_denote [] d.s.I [d.A,d.B] []
    (moveSource d) (moveTarget d) Γ (inner d hn Γ f)
  change ofTerm (moved d hn Γ f).denote =
    comp (ofTerm (inner d hn Γ f).denote) (ofTerm (moveRoute d).coproduct) at hm
  have hx := d.outer.denoteR (outerArity d hn) Γ (W4.SelectedLogical.logicalR d Γ f)
  change ofTerm (old d hn Γ f).denote =
    comp (comp (ofTerm f.denote) (ofTerm (Rules.disjRight d.s.F [] d.A d.B).toTerm))
      (ofTerm d.outer.route.coproduct) at hx
  calc
    ofTerm (repair d hn Γ f).denote =
        comp (ofTerm (inner d hn Γ f).denote)
          (comp (ofTerm (moveRoute d).coproduct)
            (comp (ofTerm (Rules.disjRight [] d.s.I d.A d.B).toTerm)
              (comp (ofTerm (block d).route.coproduct) (ofTerm d.s.e.coproduct)))) := by
      rw [ho,hb]
      change comp (comp (comp (ofTerm (moved d hn Γ f).denote)
        (ofTerm (Rules.disjRight [] d.s.I d.A d.B).toTerm))
        (ofTerm (block d).route.coproduct)) (ofTerm d.s.e.coproduct) = _
      rw [hm]
      simp only [Laws.assoc]
    _ = comp (ofTerm (inner d hn Γ f).denote)
        (comp (ofTerm (Rules.disjRight d.s.I [] d.A d.B).toTerm) (ofTerm d.last.route.coproduct)) := by
      rw [HeadRight.core_coproduct_square]
    _ = ofTerm (old d hn Γ f).denote := by
      rw [inner_denote,hx,Laws.assoc,Laws.assoc,d.coproduct_square]

theorem count : (repair d hn Γ f).cutCount = f.cutCount := by
  simp only [repair,middle,head,moved,inner,UnaryCast.exchangeR,ContractionBlock.applyR,
    G.count_reindex,G.cutCount,ContractionSelection.performR_count]
theorem old_count : (old d hn Γ f).cutCount = f.cutCount := by
  simp only [old,ContractionBlock.countR,W4.SelectedLogical.logicalR,G.cutCount]
theorem cutFree : (repair d hn Γ f).CutFree ↔ f.CutFree := by rw [G.CutFree,count]; rfl
theorem atomized : (repair d hn Γ f).Atomized ↔ f.Atomized := by
  simp only [repair,middle,head,moved,inner,UnaryCast.exchangeR,ContractionBlock.applyR,
    G.atomized_reindex,G.Atomized,ContractionSelection.performR_atomized]
theorem relation : (repair d hn Γ f).relation = (old d hn Γ f).relation :=
  congrArg occurrenceMap (denote d hn Γ f)

end DosenPetric.Reduced.Gentzen.W4.NonemptyRight
