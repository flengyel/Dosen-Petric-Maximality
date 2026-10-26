module

public import DosenPetric.GentzenRoutePrograms

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace Route
variable {K F : List (NormalForm P)} {C : NormalForm P}

/-- Separate exactly one fiber of a typed route. The residual entries retain
all original fixed tags and avoid the distinguished lower position. -/
theorem anchor_split (r : Route K F) (c : At K C) :
    ∃ (m : SelectionMask C F) (s : Route K m.erased),
      r=m.fill s c ∧ ∀ {A : NormalForm P} (a : At m.erased A),(s.get a).index≠c.index := by
  induction r with
  | nil=>exact ⟨.nil,.nil,rfl,fun a=>nomatch a⟩
  | @cons A F a r ih=>
    obtain ⟨m,s,he,hs⟩:=ih
    cases At.compare a c with
    | same=>exact ⟨.pick m,s,congrArg (Route.cons c) he,hs⟩
    | apart ha=>
      refine ⟨.fixed A m,.cons a s,congrArg (Route.cons a) he,?_⟩
      intro B b
      cases b with
      | here=>exact ha
      | there b=>exact hs b
end Route

namespace SelectionMask
variable {C : NormalForm P} {F K : List (NormalForm P)}

theorem fill_selected_iff (m : SelectionMask C F) (r : Route K m.erased) (c : At K C)
    (hr : ∀ {A : NormalForm P} (a : At m.erased A),(r.get a).index≠c.index)
    (a : At F C) : a∈m.selected ↔ (m.fill r c).get a=c := by
  induction m with
  | nil=>cases a
  | fixed B m ih=>
    cases r with | cons b r=>
      cases a with
      | here=>
        have hb:=hr (.here C m.erased)
        simp only [selected,List.mem_map,fill,Route.get]
        constructor
        · rintro ⟨x,_,he⟩;cases he
        · intro he;exact False.elim (hb (congrArg At.index he))
      | there a=>
        simpa only [selected,TraceRoute.mem_there,fill,Route.get] using
          ih r (fun {A} x=>hr x.there) a
  | pick m ih=>
    cases a with
    | here=>simp only [selected,List.mem_cons_self,fill,Route.get]
    | there a=>
      simpa only [selected,List.mem_cons,reduceCtorEq,false_or,TraceRoute.mem_there,fill,Route.get] using
        ih r hr a

/-- A nonempty fiber can be retained by an existing contraction selection.
Singleton fibers use the existing node-free operation. -/
theorem selection_of_fiber (r : Route K F) (c : At K C)
    (hn : ∃ a : At F C,r.get a=c) :
    ∃ (L : List (NormalForm P)) (p : ContractionSelection C F L) (s : Route K p.mask.erased),
      r=p.mask.fill s c ∧
      (∀ {A : NormalForm P} (a : At p.mask.erased A),(s.get a).index≠c.index) := by
  obtain ⟨m,s,hm,hs⟩:=r.anchor_split c
  have hmpos : 0<m.count := by
    obtain ⟨a,ha⟩:=hn
    have hmemb : a∈m.selected:=(m.fill_selected_iff s c hs a).mpr (hm ▸ ha)
    have hp : 0<m.selected.length:=List.length_pos_of_mem hmemb
    rwa [m.selected_count] at hp
  obtain ⟨L,p,hp⟩:=m.selection_exists hmpos
  cases hp
  exact ⟨L,p,s,hm,hs⟩
end SelectionMask
end DosenPetric.Reduced.Gentzen
