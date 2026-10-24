module

public import DosenPetric.GentzenSelectedLogicalData

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.SelectedLogical.Data
universe u
variable {P : Type u} {o : Op} (d : Data P o)

theorem categorical_square :
    (side P o).comp (d.outer.route.sideArrow o) (logicalSide o d.s.F [] d.A d.B) =
    (side P o).comp
      ((side P o).comp (d.last.route.sideArrow o) (logicalSide o d.s.I [] d.A d.B))
      (d.inner.route.sideArrow o) := by
  let C := side P o
  apply side_ext o
  intro E a
  cases At.cases_append d.s.F [d.A,d.B] a with
  | inl h =>
    obtain ⟨a,rfl⟩ := h
    rw [C.assoc,logical_prefix,Route.sideArrow_get,
      C.assoc,Route.sideArrow_get,ContractionBlock.extend_before,
      C.assoc,logical_prefix,Route.sideArrow_get,d.prefix_square]
  | inr h =>
    obtain ⟨a,rfl⟩ := h
    cases a with
    | here =>
      change C.comp (C.comp (d.outer.route.sideArrow o) (logicalSide o d.s.F [] d.A d.B))
        (component o d.a) =
        C.comp (C.comp (C.comp (d.last.route.sideArrow o) (logicalSide o d.s.I [] d.A d.B))
          (d.inner.route.sideArrow o)) (component o d.a)
      have hu : C.comp (logicalSide o d.s.F [] d.A d.B) (component o d.a) =
          C.comp (component o d.s.z) ((sideD P o).fst d.A d.B) := logical_first ..
      have hl : C.comp (logicalSide o d.s.I [] d.A d.B) (component o d.aI) =
          C.comp (component o d.q) ((sideD P o).fst d.A d.B) := logical_first ..
      rw [C.assoc,hu,← C.assoc,Route.sideArrow_get,d.s.inserted,
        C.assoc,Route.sideArrow_get,d.inner_a,C.assoc,hl,
        ← C.assoc,Route.sideArrow_get,d.last_principal]
    | there a =>
      cases a with
      | here =>
        change C.comp (C.comp (d.outer.route.sideArrow o) (logicalSide o d.s.F [] d.A d.B))
          (component o d.b) =
          C.comp (C.comp (C.comp (d.last.route.sideArrow o) (logicalSide o d.s.I [] d.A d.B))
            (d.inner.route.sideArrow o)) (component o d.b)
        have hu : C.comp (logicalSide o d.s.F [] d.A d.B) (component o d.b) =
            C.comp (component o d.s.z) ((sideD P o).snd d.A d.B) := logical_second ..
        have hl : C.comp (logicalSide o d.s.I [] d.A d.B) (component o d.bI) =
            C.comp (component o d.q) ((sideD P o).snd d.A d.B) := logical_second ..
        rw [C.assoc,hu,← C.assoc,Route.sideArrow_get,d.s.inserted,
          C.assoc,Route.sideArrow_get,d.inner_b,C.assoc,hl,
          ← C.assoc,Route.sideArrow_get,d.last_principal]
      | there a => cases a

theorem product_square (d : Data P .conj) :
    comp (ofTerm d.outer.route.product) (ofTerm (Rules.conjLeft d.s.F [] d.A d.B).toTerm) =
      comp (comp (ofTerm d.last.route.product) (ofTerm (Rules.conjLeft d.s.I [] d.A d.B).toTerm))
        (ofTerm d.inner.route.product) := by
  rw [conjLeft_compare,conjLeft_compare]
  exact d.categorical_square
theorem coproduct_square (d : Data P .disj) :
    comp (ofTerm (Rules.disjRight d.s.F [] d.A d.B).toTerm) (ofTerm d.outer.route.coproduct) =
      comp (ofTerm d.inner.route.coproduct)
        (comp (ofTerm (Rules.disjRight d.s.I [] d.A d.B).toTerm) (ofTerm d.last.route.coproduct)) := by
  rw [disjRight_compare,disjRight_compare]
  exact d.categorical_square

end DosenPetric.Reduced.Gentzen.SelectedLogical.Data
