module

public import DosenPetric.GentzenAtomicPrograms

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SelectionMask
variable {C : NormalForm P} {F : List (NormalForm P)}

/-- Embed precisely the unselected positions into the original context. -/
def fixedAt : {F : List (NormalForm P)} → (m : SelectionMask C F) →
    {A : NormalForm P} → At m.erased A → At F A
  | _,m => match m with
    | .nil => fun a => nomatch a
    | .fixed _ m => fun a => match a with
      | .here _ _ => .here _ _
      | .there a => (m.fixedAt a).there
    | .pick m => fun a => (m.fixedAt a).there

theorem fill_fixedAt {K : List (NormalForm P)} (m : SelectionMask C F)
    (r : Route K m.erased) (c : At K C) {A : NormalForm P} (a : At m.erased A) :
    (m.fill r c).get (m.fixedAt a) = r.get a := by
  induction m with
  | nil => cases a
  | fixed B m ih =>
    cases r with | cons b r =>
      cases a with
      | here => rfl
      | there a => exact ih r a
  | pick m ih => exact ih r a

theorem canonical_fixedAt (m : SelectionMask C F) {A : NormalForm P} (a : At m.erased A) :
    m.canonical.get (m.fixedAt a) = a.there := by
  rw [canonical,fill_fixedAt,Route.get_map,Route.get_identity]
end SelectionMask

namespace Route
variable {C : NormalForm P} {K F L : List (NormalForm P)}

/-- Removing a head fiber preserves exactly the preimages of every tail tag. -/
theorem factor_preimage (r : Route (C::K) F) (p : ContractionSelection C F L)
    (s : Route K p.mask.erased)
    (he : r = (p.route.map p.normalize.get).map (s.program.consFixed C).get)
    {A : NormalForm P} (a : At K A) :
    (∃ b : At p.mask.erased A, s.get b = a) ↔
      (∃ z : At F A, r.get z = a.there) := by
  have hz (z : At F A) : r.get z =
      (s.program.consFixed C).get (p.mask.canonical.get z) := by
    have hp := congrArg (fun v => v.get z) p.normalize_route
    simp only [Route.get_map] at hp
    rw [he,Route.get_map,Route.get_map,hp]
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨p.mask.fixedAt b,?_⟩
    rw [hz,p.mask.canonical_fixedAt,StructuralProgram.consFixed_there,Route.program_get,hb]
  · rintro ⟨z,h⟩
    rw [hz] at h
    cases hc : p.mask.canonical.get z with
    | here => rw [hc,StructuralProgram.consFixed_here] at h; cases h
    | there b =>
      rw [hc,StructuralProgram.consFixed_there,Route.program_get] at h
      exact ⟨b,At.there.inj h⟩

theorem factor_atomicOmissions (r : Route (C::K) F) (hr : r.AtomicOmissions)
    (p : ContractionSelection C F L) (s : Route K p.mask.erased)
    (he : r = (p.route.map p.normalize.get).map (s.program.consFixed C).get) :
    s.AtomicOmissions := by
  intro A a ha
  exact hr a.there (fun h => ha ((factor_preimage r p s he a).mpr h))

theorem dropHead_atomicOmissions (r : Route (C::K) F) (hr : r.AtomicOmissions)
    (hn : ∀ {A : NormalForm P} (a : At F A), (r.get a).index ≠ 0) :
    (r.dropHead hn).AtomicOmissions := by
  intro A a ha
  apply hr a.there
  rintro ⟨b,hb⟩
  apply ha
  refine ⟨b,?_⟩
  have he := congrArg (fun v : Route (C::K) F => v.get b) (r.dropHead_map hn)
  rw [Route.get_map,hb] at he
  exact At.there.inj he
end Route
end DosenPetric.Reduced.Gentzen
