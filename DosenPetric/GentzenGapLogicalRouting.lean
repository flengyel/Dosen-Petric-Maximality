module

public import DosenPetric.GentzenLogicalComponents
public import DosenPetric.GentzenLogicalEmbeddings

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.GapLogical.Data
universe u
variable {P : Type u} {o : Op} (d : Data P o)

theorem square_surviving {E : NormalForm P} (a : At d.U0 E) (b : At d.U1 E) (hp : d.uParent a = some b) :
    d.kParent (d.c0.get a) = some (d.c1.get b) := by
  have h := d.square a
  rw [hp,Option.map_some] at h
  exact h.symm

theorem categorical_surviving {E : NormalForm P} (a : At d.U0 E) (b : At d.U1 E) (hp : d.uParent a = some b) :
    (side P o).comp ((side P o).comp (d.c1.sideArrow o) (logicalSide o d.upBefore d.upAfter d.A d.B)) (component o a) =
    (side P o).comp ((side P o).comp (logicalSide o d.loBefore d.loAfter d.A d.B) (d.c0.sideArrow o)) (component o a) := by
  let C := side P o
  rw [C.assoc,logical_survives o d.upBefore d.upAfter d.A d.B a b hp,Route.sideArrow_get,
    C.assoc,Route.sideArrow_get,logical_survives o d.loBefore d.loAfter d.A d.B _ _ (d.square_surviving a b hp)]

theorem categorical_square :
    (side P o).comp (d.c1.sideArrow o) (logicalSide o d.upBefore d.upAfter d.A d.B) =
    (side P o).comp (logicalSide o d.loBefore d.loAfter d.A d.B) (d.c0.sideArrow o) := by
  let C := side P o
  apply side_ext o
  intro E a
  cases At.cases_append d.upBefore ([d.A,d.B] ++ d.upAfter) a with
  | inl ha =>
    obtain ⟨a,rfl⟩ := ha
    exact d.categorical_surviving _ _ (At.fixed_before ..)
  | inr ha =>
    obtain ⟨a,rfl⟩ := ha
    cases At.cases_append [d.A,d.B] d.upAfter a with
    | inr ha =>
      obtain ⟨a,rfl⟩ := ha
      exact d.categorical_surviving _ _ (At.fixed_tail ..)
    | inl ha =>
      obtain ⟨a,rfl⟩ := ha
      cases a with
      | here =>
        change C.comp (C.comp (d.c1.sideArrow o) (logicalSide o d.upBefore d.upAfter d.A d.B)) (component o d.aUpper) =
          C.comp (C.comp (logicalSide o d.loBefore d.loAfter d.A d.B) (d.c0.sideArrow o)) (component o d.aUpper)
        have hu : C.comp (logicalSide o d.upBefore d.upAfter d.A d.B) (component o d.aUpper) =
            C.comp (component o d.zUpper) ((sideD P o).fst d.A d.B) := logical_first o d.upBefore d.upAfter d.A d.B
        have hl : C.comp (logicalSide o d.loBefore d.loAfter d.A d.B) (component o d.aLower) =
            C.comp (component o d.zLower) ((sideD P o).fst d.A d.B) := logical_first o d.loBefore d.loAfter d.A d.B
        rw [C.assoc,hu,← C.assoc,Route.sideArrow_get,d.principal,C.assoc,Route.sideArrow_get,d.first,hl]
      | there a =>
        cases a with
        | there a => cases a
        | here =>
          change C.comp (C.comp (d.c1.sideArrow o) (logicalSide o d.upBefore d.upAfter d.A d.B)) (component o d.bUpper) =
            C.comp (C.comp (logicalSide o d.loBefore d.loAfter d.A d.B) (d.c0.sideArrow o)) (component o d.bUpper)
          have hu : C.comp (logicalSide o d.upBefore d.upAfter d.A d.B) (component o d.bUpper) =
              C.comp (component o d.zUpper) ((sideD P o).snd d.A d.B) := logical_second o d.upBefore d.upAfter d.A d.B
          have hl : C.comp (logicalSide o d.loBefore d.loAfter d.A d.B) (component o d.bLower) =
              C.comp (component o d.zLower) ((sideD P o).snd d.A d.B) := logical_second o d.loBefore d.loAfter d.A d.B
          rw [C.assoc,hu,← C.assoc,Route.sideArrow_get,d.principal,C.assoc,Route.sideArrow_get,d.second,hl]

theorem product_square (d : Data P .conj) :
    comp (ofTerm d.c1.product) (ofTerm (Rules.conjLeft d.upBefore d.upAfter d.A d.B).toTerm) =
    comp (ofTerm (Rules.conjLeft d.loBefore d.loAfter d.A d.B).toTerm) (ofTerm d.c0.product) := by
  rw [conjLeft_compare,conjLeft_compare]
  exact d.categorical_square

theorem coproduct_square (d : Data P .disj) :
    comp (ofTerm (Rules.disjRight d.upBefore d.upAfter d.A d.B).toTerm) (ofTerm d.c1.coproduct) =
    comp (ofTerm d.c0.coproduct) (ofTerm (Rules.disjRight d.loBefore d.loAfter d.A d.B).toTerm) := by
  rw [disjRight_compare,disjRight_compare]
  exact d.categorical_square

end DosenPetric.Reduced.Gentzen.GapLogical.Data
