module

public import DosenPetric.GentzenResidualSupport

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.Route
universe u
variable {P : Type u}

/-- Realize a route without weakening any compound formula. The recursion
removes one lower position, together with its entire fiber, at each step. -/
theorem atomic_program {K F : List (NormalForm P)} (r : Route K F)
    (hr : r.AtomicOmissions) :
    ∃ t : StructuralProgram P K F, t.Atomic ∧
      ∀ {A : NormalForm P} (a : At F A), t.get a = r.get a := by
  classical
  induction K generalizing F with
  | nil =>
    cases r with
    | nil => exact ⟨.identity [],True.intro,fun a => nomatch a⟩
    | cons a r => cases a
  | cons C K ih =>
    by_cases hn : ∃ a : At F C, r.get a = .here C K
    · obtain ⟨L,p,s,he,hsel⟩ := r.anchored_factor hn
      obtain ⟨t,ht,hget⟩ := ih s (r.factor_atomicOmissions hr p s he)
      let v : StructuralProgram P (C::K) F :=
        .seq (t.consFixed C) (.seq p.normalize.program p.programAll)
      refine ⟨v,⟨t.atomic_consFixed C ht,p.normalize.program_atomic,p.programAll_atomic⟩,?_⟩
      intro A a
      have hv : v.get a = (t.consFixed C).get (p.mask.canonical.get a) := by
        change (t.consFixed C).get (p.normalize.program.get (p.programAll.get a)) = _
        rw [p.programAll_get,p.normalize.program_get]
        have hp := congrArg (fun v => v.get a) p.normalize_route
        simp only [Route.get_map] at hp
        rw [hp]
      have hc {A : NormalForm P} (a : At (C::p.mask.erased) A) :
          (t.consFixed C).get a = (s.program.consFixed C).get a := by
        cases a with
        | here => rw [StructuralProgram.consFixed_here,StructuralProgram.consFixed_here]
        | there a =>
          rw [StructuralProgram.consFixed_there,StructuralProgram.consFixed_there,hget,Route.program_get]
      rw [hv,hc,he,Route.get_map,Route.get_map]
      have hp := congrArg (fun v => v.get a) p.normalize_route
      simp only [Route.get_map] at hp
      rw [hp]
    · have hzero : ∀ {A : NormalForm P} (a : At F A), (r.get a).index ≠ 0 := by
        intro A a hz
        cases ha : r.get a with
        | here => exact hn ⟨a,ha⟩
        | there b => rw [ha] at hz; change b.index+1 = 0 at hz; omega
      have hc : AtomicFormula C := hr (.here C K) hn
      obtain ⟨t,ht,hget⟩ := ih (r.dropHead hzero) (r.dropHead_atomicOmissions hr hzero)
      refine ⟨.seq (.thin [] K C) t,⟨hc,ht⟩,?_⟩
      intro A a
      change ((Route.thin [] K C).get (t.get a)) = r.get a
      rw [hget]
      have he := congrArg (fun v : Route (C::K) F => v.get a) (r.dropHead_map hzero)
      simpa only [Route.get_map,Route.thin,Route.get_identity] using he

theorem atomic_program_arrow {K F : List (NormalForm P)} (r : Route K F)
    (t : StructuralProgram P K F)
    (ht : ∀ {A : NormalForm P} (a : At F A), t.get a = r.get a) (o : Op) :
    t.arrow o = r.sideArrow o := by
  apply side_ext o
  intro A a
  rw [StructuralProgram.component,Route.sideArrow_get,ht]
end DosenPetric.Reduced.Gentzen.Route
