module

public import DosenPetric.GentzenHeadSelectionSplit
public import DosenPetric.GentzenHeadLogicalNaturality
public import DosenPetric.GentzenHeadLogicalBlocked

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem ContractionBlock.ext_data {F K : List (NormalForm P)}
    (d e : ContractionBlock P F K) (hc : d.C=e.C) (hg : d.gs=e.gs) (ht : d.tail=e.tail) : d=e := by
  cases d; cases e; cases hc; cases hg; cases ht; rfl

namespace W5.ParametricConjunction
variable {A B C : NormalForm P} {F K U L Γ Θ : List (NormalForm P)}
variable (p : ContractionSelection C F K) (q : ContractionSelection C U L)
variable (f : G P Γ (A::F)) (g : G P Θ (B::U))

def middle : G P (Γ++Θ) (.conj A B::(K++L)) :=
  G.conjR ((p.prependFixed [A]).performR Γ f) ((q.prependFixed [B]).performR Θ g)
def old : G P (Γ++Θ) (.conj A B::(p.erased++L)) :=
  (ContractionSelection.fixed (.conj A B) (p.chain q)).performR (Γ++Θ) (G.conjR f g)

abbrev block : ContractionBlock P (.conj A B::(K++L)) (.conj A B::(p.erased++L)) where
  C := C
  gs := [(.conj A B::gaps p.gs),p.tail++gaps q.gs]
  tail := q.tail
  upper := by
    calc
      _ = .conj A B::((gaps p.gs++C::p.tail)++(gaps q.gs++C::q.tail)) := by
        simp only [repeated,List.nil_append,List.cons_append,List.append_assoc]
      _ = _ := by rw [p.lower,q.lower]
  lower := by
    calc
      _ = .conj A B::((gaps p.gs++p.tail)++(gaps q.gs++C::q.tail)) := by
        simp only [gaps,List.append_nil,List.cons_append,List.append_assoc]
      _ = _ := by rw [p.erased_eq,q.lower]

theorem block_prepend : block (A:=A) (B:=B) p q=(p.mergeBlock q).prepend (Nat.le_refl 2) [.conj A B] := by
  apply ContractionBlock.ext_data
  · rfl
  · exact ((p.mergeBlock q).prepend_gaps (Nat.le_refl 2) [.conj A B] (gaps p.gs)
      [p.tail++gaps q.gs] rfl).symm
  · exact ((p.mergeBlock q).prepend_tail (Nat.le_refl 2) [.conj A B]).symm

def repair : G P (Γ++Θ) (.conj A B::(p.erased++L)) :=
  (block p q).applyR (Nat.le_refl 2) _ (middle p q f g)

theorem square (o : Op) :
    (ContractionSelection.fixed (.conj A B) (p.chain q)).route.sideArrow o=
      (side P o).comp ((block (A:=A) (B:=B) p q).route.sideArrow o)
        (((p.route.parallel q.route).head (.conj A B)).sideArrow o) := by
  apply side_ext o
  intro D a
  rw [(side P o).assoc,Route.sideArrow_get,Route.sideArrow_get,Route.sideArrow_get,
    block_prepend,ContractionBlock.prepend_head_route]
  apply congrArg (component o)
  cases a with
  | here => rfl
  | there a => simpa only [ContractionSelection.route,Route.head,Route.get,Route.get_map] using
      (congrArg At.there (p.chain_get q a))

theorem denote : ofTerm (repair p q f g).denote=ofTerm (old p q f g).denote := by
  have hs:=square (A:=A) (B:=B) p q .disj
  change ofTerm (ContractionSelection.fixed (.conj A B) (p.chain q)).route.coproduct=
    comp (ofTerm ((p.route.parallel q.route).head (.conj A B)).coproduct) (ofTerm (block p q).route.coproduct) at hs
  have hm : ofTerm (middle p q f g).denote=
      ofTerm (Rules.conjRight (.comp f.denote (p.route.head A).coproduct)
        (.comp g.denote (q.route.head B).coproduct)) :=
    Rules.conjRight_congr ((p.prependFixed [A]).performR_denote Γ f)
      ((q.prependFixed [B]).performR_denote Θ g)
  rw [repair,ContractionBlock.denoteR,old,ContractionSelection.performR_denote,hs,←Laws.assoc]
  exact congrArg (fun k => comp k (ofTerm (block p q).route.coproduct))
    (hm.trans (Route.head_conjRight p.route q.route f.denote g.denote).symm)

theorem blocked : BlockedR (repair p q f g) := by
  have h:=BlockedR.gammaConj C A B Γ Θ (gaps p.gs) p.tail (gaps q.gs) q.tail
    (((p.prependFixed [A]).performR Γ f).reindex rfl (congrArg (List.cons A) p.lower.symm))
    (((q.prependFixed [B]).performR Θ g).reindex rfl (congrArg (List.cons B) q.lower.symm))
  have hm:=G.conjR_reindex_inputs ((p.prependFixed [A]).performR Γ f)
    ((q.prependFixed [B]).performR Θ g) p.lower.symm q.lower.symm
  have he:=h.reindex rfl (block (A:=A) (B:=B) p q).lower
  unfold BlockedSource.right2 at he
  rw [hm] at he
  simpa only [repair,ContractionBlock.applyR,block,G.reindex_trans,middle] using he

theorem old_count : (old p q f g).cutCount=f.cutCount+g.cutCount := by
  rw [old,ContractionSelection.performR_count]; rfl
theorem repair_count : (repair p q f g).cutCount=f.cutCount+g.cutCount := by
  rw [repair,ContractionBlock.countR]
  simp only [middle,G.cutCount,ContractionSelection.performR_count]
theorem repair_cutFree : (repair p q f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,repair_count,Nat.add_eq_zero_iff]
theorem repair_atomized : (repair p q f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [repair,ContractionBlock.atomizedR,middle,G.Atomized,ContractionSelection.performR_atomized]
theorem relation : (repair p q f g).relation=(old p q f g).relation := congrArg occurrenceMap (denote p q f g)

end W5.ParametricConjunction
end DosenPetric.Reduced.Gentzen
