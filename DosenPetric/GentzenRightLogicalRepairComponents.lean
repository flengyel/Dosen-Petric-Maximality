module

public import DosenPetric.GentzenRightLogicalRepair

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W4.HeadRight
universe u
variable {P : Type u} (d : Gentzen.SelectedLogical.Data P .disj)

theorem core_square :
    (side P .disj).comp (d.last.route.sideArrow .disj) (logicalSide .disj d.s.I [] d.A d.B) =
    (side P .disj).comp (d.s.e.sideArrow .disj)
      ((side P .disj).comp ((block d).route.sideArrow .disj)
        ((side P .disj).comp (logicalSide .disj [] d.s.I d.A d.B)
          ((moveRoute d).sideArrow .disj))) := by
  let C := side P .disj
  apply side_ext .disj
  intro E a
  cases At.cases_append d.s.I [d.A,d.B] a with
  | inl h =>
    obtain ⟨a,rfl⟩ := h
    have ht : C.comp (logicalSide .disj [] d.s.I d.A d.B)
        (component .disj (At.shift [d.A,d.B] a)) =
        component .disj a.there := logical_tail .disj [] d.s.I d.A d.B a
    rw [C.assoc,logical_prefix,Route.sideArrow_get,d.last_prefix,
      C.assoc,C.assoc,C.assoc,Route.sideArrow_get,move_prefix,
      ht,Route.sideArrow_get,block_tail,Route.sideArrow_get]
  | inr h =>
    obtain ⟨a,rfl⟩ := h
    cases a with
    | here =>
      change C.comp (C.comp (d.last.route.sideArrow .disj) (logicalSide .disj d.s.I [] d.A d.B))
        (component .disj d.aI) = _
      have ht : C.comp (logicalSide .disj d.s.I [] d.A d.B) (component .disj d.aI) =
        C.comp (component .disj d.q) ((sideD P .disj).fst d.A d.B) := logical_first ..
      have hh : C.comp (logicalSide .disj [] d.s.I d.A d.B)
          (component .disj (.here d.A (d.B::d.s.I))) =
        C.comp (component .disj (.here d.C d.s.I)) ((sideD P .disj).fst d.A d.B) := logical_first ..
      have hm : (moveRoute d).get (At.shift d.s.I (.here d.A [d.B])) =
          .here d.A (d.B::d.s.I) := move_first d
      rw [C.assoc,ht,← C.assoc,Route.sideArrow_get,d.last_principal,
        C.assoc,C.assoc,C.assoc,Route.sideArrow_get,hm,hh,
        ← C.assoc ((block d).route.sideArrow .disj),Route.sideArrow_get,block_fresh,
        ← C.assoc (d.s.e.sideArrow .disj),Route.sideArrow_get,d.s.retained]
    | there a =>
      cases a with
      | here =>
        change C.comp (C.comp (d.last.route.sideArrow .disj) (logicalSide .disj d.s.I [] d.A d.B))
          (component .disj d.bI) = _
        have ht : C.comp (logicalSide .disj d.s.I [] d.A d.B) (component .disj d.bI) =
          C.comp (component .disj d.q) ((sideD P .disj).snd d.A d.B) := logical_second ..
        have hh : C.comp (logicalSide .disj [] d.s.I d.A d.B)
            (component .disj (.there (.here d.B d.s.I))) =
          C.comp (component .disj (.here d.C d.s.I)) ((sideD P .disj).snd d.A d.B) := logical_second ..
        have hm : (moveRoute d).get (At.shift d.s.I (.there (.here d.B []))) =
            .there (.here d.B d.s.I) := move_second d
        rw [C.assoc,ht,← C.assoc,Route.sideArrow_get,d.last_principal,
          C.assoc,C.assoc,C.assoc,Route.sideArrow_get,hm,hh,
          ← C.assoc ((block d).route.sideArrow .disj),Route.sideArrow_get,block_fresh,
          ← C.assoc (d.s.e.sideArrow .disj),Route.sideArrow_get,d.s.retained]
      | there a => cases a

theorem core_coproduct_square :
    comp (ofTerm (moveRoute d).coproduct)
      (comp (ofTerm (Rules.disjRight [] d.s.I d.A d.B).toTerm)
        (comp (ofTerm (block d).route.coproduct) (ofTerm d.s.e.coproduct))) =
    comp (ofTerm (Rules.disjRight d.s.I [] d.A d.B).toTerm) (ofTerm d.last.route.coproduct) := by
  rw [disjRight_compare,disjRight_compare]
  change comp (ofTerm (moveRoute d).coproduct)
      (comp (ofTerm (logicalCompare .disj [] d.s.I d.A d.B).invTerm)
        (comp (ofTerm (block d).route.coproduct) (ofTerm d.s.e.coproduct))) =
    comp (ofTerm (logicalCompare .disj d.s.I [] d.A d.B).invTerm) (ofTerm d.last.route.coproduct)
  have h := core_square d
  change comp (ofTerm (logicalCompare .disj d.s.I [] d.A d.B).invTerm)
      (ofTerm d.last.route.coproduct) =
    comp (comp (comp (ofTerm (moveRoute d).coproduct)
      (ofTerm (logicalCompare .disj [] d.s.I d.A d.B).invTerm))
      (ofTerm (block d).route.coproduct)) (ofTerm d.s.e.coproduct) at h
  exact (by simpa only [Laws.assoc] using h.symm)

theorem denote (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ d.F) :
    ofTerm (repairR d hn Γ f).denote = ofTerm (W4.SelectedLogical.oldR d hn Γ f).denote := by
  have ho := UnaryCast.exchangeR_denote (gaps d.gs) [d.C] d.Θ []
    d.s.exchangeSource d.s.exchangeTarget Γ (blockedR d hn Γ f)
  change ofTerm (repairR d hn Γ f).denote =
    comp (ofTerm (blockedR d hn Γ f).denote) (ofTerm d.s.e.coproduct) at ho
  have hb := (block d).denoteR (Nat.le_refl 2) Γ (headR d hn Γ f)
  change ofTerm (blockedR d hn Γ f).denote =
    comp (ofTerm (headR d hn Γ f).denote) (ofTerm (block d).route.coproduct) at hb
  have hm := UnaryCast.exchangeR_denote [] d.s.I [d.A,d.B] []
    (moveSource d) (moveTarget d) Γ (W4.SelectedLogical.innerR d hn Γ f)
  change ofTerm (movedR d hn Γ f).denote =
    comp (ofTerm (W4.SelectedLogical.innerR d hn Γ f).denote)
      (ofTerm (moveRoute d).coproduct) at hm
  have ht := d.last.denoteR (Nat.le_refl 2) Γ (W4.SelectedLogical.middleR d hn Γ f)
  change ofTerm (W4.SelectedLogical.newR d hn Γ f).denote =
    comp (comp (ofTerm (W4.SelectedLogical.innerR d hn Γ f).denote)
      (ofTerm (Rules.disjRight d.s.I [] d.A d.B).toTerm))
      (ofTerm d.last.route.coproduct) at ht
  calc
    ofTerm (repairR d hn Γ f).denote =
        comp (ofTerm (W4.SelectedLogical.innerR d hn Γ f).denote)
          (comp (ofTerm (moveRoute d).coproduct)
            (comp (ofTerm (Rules.disjRight [] d.s.I d.A d.B).toTerm)
              (comp (ofTerm (block d).route.coproduct) (ofTerm d.s.e.coproduct)))) := by
      rw [ho,hb]
      change comp (comp (comp (ofTerm (movedR d hn Γ f).denote)
        (ofTerm (Rules.disjRight [] d.s.I d.A d.B).toTerm))
        (ofTerm (block d).route.coproduct)) (ofTerm d.s.e.coproduct) = _
      rw [hm]
      simp only [Laws.assoc]
    _ = ofTerm (W4.SelectedLogical.newR d hn Γ f).denote := by
      rw [core_coproduct_square,← Laws.assoc,← ht]
    _ = ofTerm (W4.SelectedLogical.oldR d hn Γ f).denote := W4.SelectedLogical.denoteR ..

end DosenPetric.Reduced.Gentzen.W4.HeadRight
