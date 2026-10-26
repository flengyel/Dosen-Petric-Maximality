module

public import DosenPetric.GentzenStructuralProgramBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace At

def dropHead {K : List (NormalForm P)} {A C : NormalForm P}
    (a : At (C::K) A) (h : a.index≠0) : At K A :=
  match a,h with
  | .there b,_=>b

theorem dropHead_there {K : List (NormalForm P)} {A C : NormalForm P}
    (a : At (C::K) A) (h : a.index≠0) : (a.dropHead h).there=a := by
  cases a with
  | here=>exact False.elim (h rfl)
  | there=>rfl
end At
namespace Route
variable {C : NormalForm P} {K F : List (NormalForm P)}

def dropHead : {F : List (NormalForm P)}→(r : Route (C::K) F)→
    (∀ {A : NormalForm P} (a : At F A),(r.get a).index≠0)→Route K F
  | _,.nil,_=>.nil
  | _,.cons a r,h=>.cons (a.dropHead (h (.here _ _))) (r.dropHead (fun a=>h a.there))

theorem dropHead_map (r : Route (C::K) F)
    (h : ∀ {A : NormalForm P} (a : At F A),(r.get a).index≠0) :
    (r.dropHead h).map (fun a=>a.there)=r := by
  induction r with
  | nil=>rfl
  | cons a r ih=>
    change Route.cons (a.dropHead _).there ((r.dropHead _).map (fun a=>a.there))=Route.cons a r
    exact (congrArg (fun b=>Route.cons b ((r.dropHead _).map (fun a=>a.there)))
      (At.dropHead_there a (h (.here _ _)))).trans
      (congrArg (Route.cons a) (ih (fun a=>h a.there)))
end Route
namespace ContractionSelection
variable {C : NormalForm P} {F K : List (NormalForm P)}

theorem normalize_route (p : ContractionSelection C F K) :
    p.route.map p.normalize.get=p.mask.canonical := by
  apply Route.ext_get
  intro A a
  rw [Route.get_map]
  apply At.index_injective
  exact (p.normalize_index a).trans (p.mask.canonical_index a).symm
end ContractionSelection
namespace SelectionMask
variable {C : NormalForm P} {F L : List (NormalForm P)}

theorem canonical_program (m : SelectionMask C F) (s : Route L m.erased) :
    m.canonical.map (s.program.consFixed C).get=
      m.fill (s.map (fun a=>a.there)) (.here C L) := by
  rw [canonical,fill_map,StructuralProgram.consFixed_here]
  have he : ((Route.identity m.erased).map (fun a=>a.there)).map (s.program.consFixed C).get=
      s.map (fun a=>a.there) := by
    apply Route.ext_get
    intro A a
    rw [Route.get_map,Route.get_map,Route.get_identity,
      StructuralProgram.consFixed_there,Route.program_get,Route.get_map]
  rw [he]
end SelectionMask

namespace Route
variable {C : NormalForm P} {F K : List (NormalForm P)}

/-- Any nonempty selected fiber can be performed first. All remaining
structural operations act in the fixed tail below the distinguished head. -/
theorem anchored_factor (r : Route (C::K) F)
    (hn : ∃ a : At F C,r.get a=.here C K) :
    ∃ (L : List (NormalForm P)) (p : ContractionSelection C F L)
      (s : Route K p.mask.erased),
      r=(p.route.map p.normalize.get).map (s.program.consFixed C).get ∧
      (∀ a : At F C,a∈p.selected ↔ r.get a=.here C K) := by
  obtain ⟨L,p,t,he,ht⟩:=SelectionMask.selection_of_fiber r (.here C K) hn
  have ht0 : ∀ {A : NormalForm P} (a : At p.mask.erased A),(t.get a).index≠0:=ht
  let s:=t.dropHead ht0
  refine ⟨L,p,s,?_,?_⟩
  · rw [p.normalize_route,SelectionMask.canonical_program]
    exact he.trans (congrArg (fun t=>p.mask.fill t (.here C K)) (t.dropHead_map ht0).symm)
  · intro a
    rw [←p.mask_selected]
    have hh:=p.mask.fill_selected_iff t (.here C K) ht a
    rw [←he] at hh
    exact hh
end Route
end DosenPetric.Reduced.Gentzen
