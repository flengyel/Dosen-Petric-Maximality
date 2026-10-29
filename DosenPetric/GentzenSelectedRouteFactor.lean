module

public import DosenPetric.GentzenBlockedMixRoutes
public import DosenPetric.GentzenResidualPositions

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.Route
universe u
variable {P : Type u} {K U : List (NormalForm P)} {C : NormalForm P}

/-- Erase one selected position from a route whose other positions stay fixed. -/
def selectedResidual (r : Route K U) (x : At K C) (a : At U C)
    (hf : ∀ {B : NormalForm P} (b : At a.erase B),
      (r.get (a.retain b)).index ≠ x.index) : Route x.erase a.erase :=
  (identity a.erase).map (fun b => x.remove (r.get (a.retain b)) (hf b))

theorem selectedResidual_get (r : Route K U) (x : At K C) (a : At U C)
    (hf : ∀ {B : NormalForm P} (b : At a.erase B),
      (r.get (a.retain b)).index ≠ x.index) {B : NormalForm P} (b : At a.erase B) :
    x.retain ((selectedResidual r x a hf).get b) = r.get (a.retain b) := by
  rw [selectedResidual,get_map,get_identity,At.retain_remove]

/-- The selected head and every other positional component factor separately. -/
theorem selected_factor (o : Op) (r : Route K U) (x : At K C) (a : At U C)
    (p : Route x.erase a.erase) (ha : r.get a = x)
    (hp : ∀ {B : NormalForm P} (b : At a.erase B),
      r.get (a.retain b) = x.retain (p.get b)) :
    (side P o).comp (x.toHead.arrow o) (r.sideArrow o) =
      (side P o).comp ((sideM P o).tensor ((side P o).id C) (p.sideArrow o))
        (a.toHead.arrow o) := by
  let S := side P o
  let D := sideD P o
  apply side_ext o
  intro B b
  rw [S.assoc,sideArrow_get,ExchangeScript.component,
    S.assoc,ExchangeScript.component]
  by_cases hi : b.index = a.index
  · have he := b.formula_eq a hi
    cases he
    have hb : b = a := At.index_injective b a hi
    cases hb
    rw [ha,At.toHead_get,At.toHead_get,component_here,component_here,← D.fst_nat,S.comp_id]
  · obtain ⟨b,rfl⟩ : ∃ b' : At a.erase B, b = a.retain b' :=
      ⟨a.remove b hi,(a.retain_remove b hi).symm⟩
    rw [hp,At.toHead_get_retain,At.toHead_get_retain,component_there,component_there,
      ← S.assoc,← D.snd_nat,S.assoc,sideArrow_get]

end DosenPetric.Reduced.Gentzen.Route
