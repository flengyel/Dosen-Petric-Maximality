module

public import DosenPetric.GentzenEconomicalRoutes

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionSelection
variable {C : NormalForm P} {F K : List (NormalForm P)}

theorem route_surjective (p : ContractionSelection C F K) {A : NormalForm P} (a : At K A) :
    ∃ b : At F A, p.route.get b = a := by
  induction p with
  | last Θ => exact ⟨a,Route.get_identity a⟩
  | fixed B p ih =>
    cases a with
    | here => exact ⟨.here _ _,rfl⟩
    | there a =>
      obtain ⟨b,hb⟩ := ih a
      exact ⟨b.there,by simpa only [route,Route.get,Route.get_map] using congrArg At.there hb⟩
  | more p ih =>
    obtain ⟨b,hb⟩ := ih a
    exact ⟨b.there,hb⟩
end ContractionSelection

namespace Route
variable {F U K L : List (NormalForm P)}

theorem atomicOmissions_map (r : Route U F) (hr : r.AtomicOmissions)
    (f : ∀ {A : NormalForm P}, At U A → At K A)
    (hf : ∀ {A : NormalForm P} (a : At K A), ∃ b : At U A, f b = a) :
    (r.map f).AtomicOmissions := by
  intro A a ha
  obtain ⟨b,hb⟩ := hf a
  apply hr b
  rintro ⟨c,hc⟩
  exact ha ⟨c,by rw [Route.get_map,hc,hb]⟩

theorem exchange_atomicOmissions (Γ X Y Θ : List (NormalForm P)) :
    (Route.exchange Γ X Y Θ).AtomicOmissions := by
  intro A a ha
  apply False.elim
  apply ha
  refine ⟨a.swapBlocks Γ Y X Θ,?_⟩
  rw [Route.exchange_get]
  exact At.swapBlocks_inverse Γ Y X Θ a

theorem copies_atomicOmissions (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ : List (NormalForm P)) (hn : 2 ≤ gs.length) : (copies C gs Θ).AtomicOmissions := by
  let d : ContractionBlock P (repeated C gs++Θ) (gaps gs++C::Θ) := ⟨C,gs,Θ,rfl,rfl⟩
  let p := d.selection (d.nonempty hn)
  have he : p.route = copies C gs Θ := by
    rw [p.route_eq,d.selection_block]
    rfl
  intro A a ha
  exact False.elim (ha (he ▸ p.route_surjective a))

theorem thin_atomicOmissions (Γ Θ : List (NormalForm P)) (C : NormalForm P)
    (hc : AtomicFormula C) : (Route.thin Γ Θ C).AtomicOmissions := by
  induction Γ with
  | nil =>
    intro A a ha
    cases a with
    | here => exact hc
    | there a => exact False.elim (ha ⟨a,by rw [thin,Route.get_map,Route.get_identity]⟩)
  | cons B Γ ih =>
    intro A a ha
    cases a with
    | here => exact False.elim (ha ⟨.here _ _,rfl⟩)
    | there a =>
      apply ih a
      rintro ⟨b,hb⟩
      exact ha ⟨b.there,by simpa only [thin,Route.get,Route.get_map] using congrArg At.there hb⟩

/-- The normalized output of a real contraction selection has no additional
unused compound positions. -/
theorem selection_atomicOmissions {C : NormalForm P} (q : ContractionSelection C U K)
    (r : Route U F) (hr : r.AtomicOmissions) :
    ((r.map q.route.get).map q.normalize.get).AtomicOmissions := by
  apply (r.map q.route.get).atomicOmissions_map
    (r.atomicOmissions_map hr q.route.get q.route_surjective) q.normalize.get
  intro A a
  exact ⟨q.normalize.inverse.get a,q.normalize.get_inverse a⟩
end Route
end DosenPetric.Reduced.Gentzen
