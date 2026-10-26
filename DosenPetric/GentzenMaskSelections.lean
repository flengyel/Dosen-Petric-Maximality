module

public import DosenPetric.GentzenSelectionMasks
public import DosenPetric.GentzenSelectionAssociativity

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SelectionMask
variable {C : NormalForm P} {F U L : List (NormalForm P)}

theorem selection_exists (m : SelectionMask C F) (h : 0<m.count) :
    ∃ (K : List (NormalForm P)) (p : ContractionSelection C F K), p.mask=m := by
  induction m with
  | nil=>change 0<0 at h;omega
  | fixed A m ih=>
    obtain ⟨K,p,hp⟩:=ih h
    exact ⟨A::K,.fixed A p,congrArg (fixed A) hp⟩
  | @pick F m ih=>
    by_cases hz : m.count=0
    · have hm:=m.zero_fixed hz
      cases hm
      exact ⟨C::F,.last F,rfl⟩
    · obtain ⟨K,p,hp⟩:=ih (by omega)
      exact ⟨K,.more p,congrArg pick hp⟩

/-- Delete the selected positions in the prefix, routing them all to the
retained copy of the nonempty suffix selection. -/
def lead : {F U L : List (NormalForm P)}→(m : SelectionMask C F)→
    ContractionSelection C U L→ContractionSelection C (F++U) (m.erased++L)
  | _,_,_,.nil,q=>q
  | _,_,_,.fixed A m,q=>.fixed A (m.lead q)
  | _,_,_,.pick m,q=>.more (m.lead q)

theorem lead_mask (m : SelectionMask C F) (q : ContractionSelection C U L) :
    (m.lead q).mask=m.append q.mask := by
  induction m with
  | nil=>rfl
  | fixed A m ih=>exact congrArg (fixed A) ih
  | pick m ih=>exact congrArg pick ih

theorem lead_keep (m : SelectionMask C F) (q : ContractionSelection C U L) :
    (m.lead q).keep=At.shift m.erased q.keep := by
  induction m with
  | nil=>rfl
  | fixed A m ih=>exact congrArg At.there ih
  | pick m ih=>exact ih

theorem lead_erased (m : SelectionMask C F) (q : ContractionSelection C U L) :
    (m.lead q).erased=m.erased++q.erased := by
  induction m with
  | nil=>rfl
  | fixed A m ih=>exact congrArg (List.cons A) ih
  | pick m ih=>exact ih
end SelectionMask

namespace ContractionSelection
variable {C : NormalForm P} {F K L : List (NormalForm P)}

theorem mask_match (p : ContractionSelection C F K) (q : ContractionSelection C F L)
    (h : p.mask=q.mask) : ∃ hK : K=L, p.cast rfl hK=q := by
  induction p generalizing L with
  | last Θ=>
    cases q with
    | last=>exact ⟨rfl,rfl⟩
    | fixed A q=>cases h
    | more q=>
      have hm : SelectionMask.allFixed Θ=q.mask := SelectionMask.pick.inj h
      have hc:=congrArg SelectionMask.count hm
      rw [SelectionMask.allFixed_count,q.mask_count] at hc
      have hq:=q.arity_pos
      omega
  | fixed A p ih=>
    cases q with
    | last=>cases h
    | fixed A q=>
      obtain ⟨hk,he⟩:=ih q (SelectionMask.fixed.inj h)
      cases hk;cases he
      exact ⟨rfl,rfl⟩
    | more q=>cases h
  | more p ih=>
    cases q with
    | last=>
      have hc:=congrArg SelectionMask.count h
      simp only [mask,SelectionMask.count,SelectionMask.allFixed_count,mask_count] at hc
      have hp:=p.arity_pos
      omega
    | fixed A q=>cases h
    | more q=>
      obtain ⟨hk,he⟩:=ih q (SelectionMask.pick.inj h)
      cases hk;cases he
      exact ⟨rfl,rfl⟩

/-- The route of fixed positions, with the retained selected slot omitted. -/
def erasedRoute : {F K : List (NormalForm P)}→(p : ContractionSelection C F K)→Route K p.erased
  | _,_,.last Θ=>(Route.identity Θ).map (fun a=>a.there)
  | _,_,.fixed A p=>.cons (.here A _) (p.erasedRoute.map (fun a=>a.there))
  | _,_,.more p=>p.erasedRoute

end ContractionSelection
namespace Route

theorem cast_cons {A : NormalForm P} {F U K : List (NormalForm P)} (h : F=U)
    (a : At K A) (r : Route K F) :
    (Route.cons a r).cast rfl (congrArg (List.cons A) h)=Route.cons a (r.cast rfl h) := by
  cases h;rfl

theorem cast_map {F U K L : List (NormalForm P)} (h : F=U) (r : Route K F)
    (f : ∀ {A : NormalForm P},At K A→At L A) :
    (r.map f).cast rfl h=(r.cast rfl h).map f := by
  cases h;rfl
end Route
namespace SelectionMask
variable {C : NormalForm P} {K : List (NormalForm P)}

theorem fill_fixed_cast {F T : List (NormalForm P)} (A : NormalForm P)
    (m : SelectionMask C F) (h : T=m.erased) (a : At K A) (r : Route K T) (c : At K C) :
    (fixed A m).fill ((Route.cons a r).cast rfl (congrArg (List.cons A) h)) c=
      Route.cons a (m.fill (r.cast rfl h) c) := by
  cases h;rfl

theorem fill_allFixed (F : List (NormalForm P)) (r : Route K F) (c : At K C) :
    (allFixed F).fill (r.cast rfl (allFixed_erased F).symm) c=r := by
  induction F with
  | nil=>cases r;rfl
  | cons A F ih=>
    cases r with
    | cons a r=>
      change (fixed A (allFixed F)).fill
        ((Route.cons a r).cast rfl (congrArg (List.cons A) (allFixed_erased F).symm)) c=Route.cons a r
      rw [fill_fixed_cast A (allFixed F) (allFixed_erased F).symm]
      exact congrArg (Route.cons a) (ih r)
end SelectionMask
namespace ContractionSelection
variable {C : NormalForm P} {F K : List (NormalForm P)}

theorem route_fill (p : ContractionSelection C F K) :
    p.route=p.mask.fill (p.erasedRoute.cast rfl p.mask_erased.symm) p.keep := by
  induction p with
  | last Θ=>
    change Route.cons (.here C Θ) ((Route.identity Θ).map (fun a=>a.there))=
      Route.cons (.here C Θ) ((SelectionMask.allFixed Θ).fill
        (((Route.identity Θ).map (fun a=>a.there)).cast rfl (SelectionMask.allFixed_erased Θ).symm) (.here C Θ))
    rw [SelectionMask.fill_allFixed]
  | fixed A p ih=>
    change Route.cons (.here A _) (p.route.map (fun a=>a.there))=
      (SelectionMask.fixed A p.mask).fill
        ((Route.cons (.here A _) (p.erasedRoute.map (fun a=>a.there))).cast rfl
          (congrArg (List.cons A) p.mask_erased.symm)) p.keep.there
    rw [SelectionMask.fill_fixed_cast A p.mask p.mask_erased.symm]
    rw [Route.cast_map,←SelectionMask.fill_map]
    exact congrArg (fun r=>Route.cons (.here A _) (r.map (fun a=>a.there))) ih
  | more p ih=>exact congrArg (Route.cons p.keep) ih
end ContractionSelection
end DosenPetric.Reduced.Gentzen
