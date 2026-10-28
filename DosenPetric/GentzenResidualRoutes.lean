module

public import DosenPetric.GentzenResidualPositions

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace Route
variable {K U : List (NormalForm P)} {C : NormalForm P}

/-- Exactly one upper tag maps to the selected lower tag, including its ordinal coordinate. -/
def SingleFiber (r : Route K U) (x : At K C) (y : At U C) : Prop :=
  r.get y = x ∧ ∀ {E : NormalForm P} (b : At U E),
    (r.get b).index = x.index → b.index = y.index

theorem residual_ne (r : Route K U) (x : At K C) (y : At U C)
    (h : r.SingleFiber x y) {E : NormalForm P} (b : At y.erase E) :
    (r.get (y.retain b)).index ≠ x.index := by
  intro e
  exact y.retain_ne b (h.2 _ e)

/-- Delete the selected singleton fiber and retain every other typed tag. -/
def residual (r : Route K U) (x : At K C) (y : At U C) (h : r.SingleFiber x y) :
    Route x.erase y.erase :=
  tabulate x.erase y.erase (fun b => x.remove (r.get (y.retain b)) (r.residual_ne x y h b))

theorem residual_get (r : Route K U) (x : At K C) (y : At U C)
    (h : r.SingleFiber x y) {E : NormalForm P} (b : At y.erase E) :
    x.retain ((r.residual x y h).get b) = r.get (y.retain b) := by
  rw [residual, get_tabulate, At.retain_remove]

/-- The exact head-routing square for a structural map with one selected predecessor. -/
theorem residual_square (r : Route K U) (x : At K C) (y : At U C)
    (h : r.SingleFiber x y) (o : Op) :
    (side P o).comp (x.toHead.arrow o) (r.sideArrow o) =
      (side P o).comp ((sideM P o).tensor ((side P o).id C) ((r.residual x y h).sideArrow o))
        (y.toHead.arrow o) := by
  let S := side P o
  let D := sideD P o
  apply side_ext o
  intro E b
  rw [S.assoc, sideArrow_get, ExchangeScript.component, S.assoc, ExchangeScript.component]
  by_cases hb : b.index = y.index
  · have he := b.formula_eq y hb
    cases he
    have he : b = y := by apply At.index_injective; exact hb
    cases he
    rw [h.1, At.toHead_get, At.toHead_get, component_here, component_here, ← D.fst_nat, S.comp_id]
  · let a := y.remove b hb
    have hy : y.retain a = b := y.retain_remove b hb
    have hx : x.retain ((r.residual x y h).get a) = r.get b := by
      rw [residual_get, hy]
    rw [← hx, At.toHead_get_retain, ← hy, At.toHead_get_retain, component_there, component_there]
    rw [← S.assoc, ← D.snd_nat, S.assoc, sideArrow_get]

end Route
end DosenPetric.Reduced.Gentzen
